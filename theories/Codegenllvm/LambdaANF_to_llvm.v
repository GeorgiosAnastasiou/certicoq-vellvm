Unset Universe Checking.

From Coq Require Import Strings.String BinNums ZArith List FMapAVL Floats.
From ExtLib Require Import Monads.
Import MonadNotation.

From CertiCoq.LambdaANF Require Import cps toplevel cps_util cps_show.
From CertiCoq.Common Require Import Common Pipeline_utils compM.
From MetaCoq.Utils Require Import MCString.
(* Require Import PTree. *)

(* Vellvm AST *)
From Vellvm.Syntax Require Import LLVMAst.

Open Scope string_scope.
Open Scope monad_scope.
Open Scope Z_scope.
Require Import compcert.lib.Maps.

(* these definitions were used in the dummy compiler, TODO remove *)
Definition int_ty : LLVMAst.typ := TYPE_I 64%positive.  (* 64-bit int type *)

Definition const_int (z : Z) : LLVMAst.texp LLVMAst.typ :=
  (int_ty, EXP_Integer z).

Definition i32_42 : texp typ :=
  (TYPE_I 32%positive, EXP_Integer 42%Z).

Definition ret_block : block typ :=
  mk_block (Name "entry") [] [] (TERM_Ret i32_42) None.

Definition main_decl : declaration typ :=
  mk_declaration
    (Name "main")
    (TYPE_Function (TYPE_I 32%positive) [] false)
    ([],[]) [] [].

Definition main_def : definition typ (block typ * list (block typ)) :=
  {| df_prototype := main_decl
   ; df_args      := []
   ; df_instrs    := (ret_block, [])
  |}.

Definition trivial_module_ast
  : list (toplevel_entity
            typ
            (block typ * list (block typ))) :=
  [ TLE_Definition main_def ].


(** on Vellvm, a module is a list of TLEs like functions, globals. **)
(* list of toplevel entity typ of (entry block, other blocks), each of which has
type (block, typ) *)
Module VellvmMod.
  Definition t : Set :=
    list (LLVMAst.toplevel_entity
            LLVMAst.typ
            (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))).
End VellvmMod.

(*  Useful definitions from certicoqwasm project *)
(* 1. *)
Definition get_ctor_arity (cenv : ctor_env) (t : ctor_tag) :=
  match M.get t cenv with
  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
  | _ => Err "found constructor without ctor_arity set"
  end.

(* 2. *)
Definition collect_function_vars (e : cps.exp) : list cps.var :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : list cps.var :=
          match fds with
          | Fnil => []
          | Fcons x _ _ e' fds' => x :: (iter fds')
          end) fds
    | _ => []
    end.

(* environment that maps LambdaANF variables to llvm identifiers.
   Kept around for later *)
Definition local_env := PTree.t raw_id.

(* positive / nat -> stdlib string (the type Vellvm's [Name] expects). The C
   name in prim_env and MCString produce MetaCoq bytestrings, so, convert. *)
Definition pos_to_str (p : positive) : String.string :=
  bytestring.String.to_string (MCString.string_of_positive p).
Definition nat_to_str (n : nat) : String.string :=
  bytestring.String.to_string (MCString.string_of_nat n).

(* Map a LambdaANF variable to a *named* Vellvm identifier "%v<n>". *)
Definition var_to_id (x : var) : raw_id := Name (("v" ++ pos_to_str x)%string).



(** * Value representation 
mirrors LambdaANF_to_Clight. 
Will need to be updated with GC. 
*)

Definition word_t   : typ := TYPE_I 64%positive.
Definition wordptr_t : typ := TYPE_Pointer (Some word_t).
Definition i8_t     : typ := TYPE_I 8%positive.
Definition i8ptr_t  : typ := TYPE_Pointer (Some i8_t).

Inductive ctor_rep : Set :=
| rep_enum  (ord : N)            (* unboxed, nullary constructor *)
| rep_boxed (ord : N) (arity : N). (* boxed, arity > 0 *)

Definition get_ctor_rep (cenv : ctor_env) (t : ctor_tag) : error ctor_rep :=
  match M.get t cenv with
  | Some info =>
      if (ctor_arity info =? 0)%N
      then Ret (rep_enum (ctor_ordinal info))
      else Ret (rep_boxed (ctor_ordinal info) (ctor_arity info))
  | None => Err "get_ctor_rep: constructor tag not found in ctor_env"
  end.

Definition enum_immediate (ord : N) : Z := (Z.shiftl (Z.of_N ord) 1 + 1)%Z.
Definition boxed_header (ord arity : N) : Z := (Z.shiftl (Z.of_N arity) 10 + Z.of_N ord)%Z.

(* CertiCoq's boxed-float header tag  *)
Definition float_header : Z := 1277%Z.


Definition f64_join_bits (s : bool) (m e : Z) : Z :=
  (Z.shiftl ((if s then Z.pow 2 11 else 0) + e) 52 + m)%Z.

Definition bits_of_spec_float (x : SpecFloat.spec_float) : Z :=
  match x with
  | SpecFloat.S754_zero s       => f64_join_bits s 0 0
  | SpecFloat.S754_infinity s   => f64_join_bits s 0 (Z.pow 2 11 - 1)
  | SpecFloat.S754_nan          => f64_join_bits false (Z.pow 2 51) (Z.pow 2 11 - 1)
  | SpecFloat.S754_finite s m e =>
      let mm := (Z.pos m - Z.pow 2 52)%Z in
      if Z.leb 0 mm
      then f64_join_bits s mm (e + 1075)     (* normalized: e - emin + 1 *)
      else f64_join_bits s (Z.pos m) 0       
  end.

Definition float_to_bits (f : PrimFloat.float) : Z :=
  bits_of_spec_float (FloatOps.Prim2SF f).

(* the i64 operand holding the value of a LambdaANF variable *)
Definition var_operand (x : var) : texp typ := (word_t, EXP_Ident (ID_Local (var_to_id x))).


Definition cg_code := list (instr_id * instr typ).


Definition genM (A : Type) : Type := Z -> error (A * cg_code * list (block typ) * Z).

Definition gen_ret {A} (a : A) : genM A := fun s => Ret (a, [], [], s).

Definition gen_bind {A B} (m : genM A) (f : A -> genM B) : genM B :=
  fun s =>
    match m s with
    | Err e => Err e
    | Ret (a, c1, b1, s1) =>
        match f a s1 with
        | Err e => Err e
        | Ret (b, c2, b2, s2) => Ret (b, (c1 ++ c2)%list, (b1 ++ b2)%list, s2)
        end
    end.

#[global] Instance Monad_genM : Monad genM :=
  { ret := @gen_ret ; bind := @gen_bind }.

Definition gen_fail {A} (msg : string) : genM A := fun _ => Err msg.

Definition lift_err {A} (e : error A) : genM A :=
  fun s => match e with Ret a => Ret (a, [], [], s) | Err m => Err m end.

(* fresh named SSA id "%t<n>" for an intermediate value or a block label;
   disjoint from source variables' "%v<n>" ids (see [var_to_id]) *)
Definition fresh_id : genM raw_id :=
  fun s => Ret (Name (("t" ++ nat_to_str (Z.to_nat s))%string), [], [], (s + 1)%Z).
(* fresh number for a void instruction id (store) *)
Definition fresh_void : genM int_ast := fun s => Ret (s, [], [], (s + 1)%Z).

Definition emit (i : instr_id * instr typ) : genM Datatypes.unit := fun s => Ret (tt, [i], [], s).

(* add an already-completed basic block to the output *)
Definition emit_block (b : block typ) : genM Datatypes.unit := fun s => Ret (tt, [], [b], s).

(* run [m] but return its current-block code instead of merging it into the
   surrounding block; completed blocks and the counter still propagate. Used to
   collect the body of an Ecase arm into its own block. *)
Definition capture {A} (m : genM A) : genM (cg_code * A) :=
  fun s =>
    match m s with
    | Err e => Err e
    | Ret (a, code, blks, s') => Ret ((code, a), [], blks, s')
    end.

(* emit an operation producing a fresh local; return its operand expression *)
Definition emit_op (op : exp typ) : genM (exp typ) :=
  id <- fresh_id ;;
  emit (IId id, INSTR_Op op) ;;
  ret (EXP_Ident (ID_Local id)).

(* bind a LambdaANF variable [x] to the result of operation [op] *)
Definition bind_var_op (x : var) (op : exp typ) : genM Datatypes.unit :=
  emit (IId (var_to_id x), INSTR_Op op).

Definition malloc_fn : texp typ :=
  (i8ptr_t, EXP_Ident (ID_Global (Name "malloc"))).

(* Build a function declaration with empty per-argument attributes. ShowAST
   requires the args-attrs list to have exactly one entry per argument (it
  combines them, and the definition printer errors on a length mismatch). *)
Definition mk_fun_decl (name : raw_id) (ret : typ) (argtys : list typ) : declaration typ :=
  mk_declaration name (TYPE_Function ret argtys false)
                 ([], List.repeat (@nil param_attr) (List.length argtys)) [] [].

Definition malloc_decl : declaration typ :=
  mk_fun_decl (Name "malloc") i8ptr_t [word_t].

(* call malloc for [nbytes] and return the i64* base pointer *)
Definition gen_alloc (nbytes : Z) : genM (exp typ) :=
  raw  <- (id <- fresh_id ;;
           emit (IId id, INSTR_Call malloc_fn [((word_t, EXP_Integer nbytes), [])] []) ;;
           ret (EXP_Ident (ID_Local id))) ;;
  emit_op (OP_Conversion Bitcast i8ptr_t raw wordptr_t).

(* store [val] at i64* [ptr] *)
Definition gen_store (ptr : exp typ) (val : texp typ) : genM Datatypes.unit :=
  n <- fresh_void ;;
  emit (IVoid n, INSTR_Store val (wordptr_t, ptr) []).

(* getelementptr i64, i64* [ptr], i64 [i] -> i64* to element [i] *)
Definition gen_gep (ptr : exp typ) (i : Z) : genM (exp typ) :=
  emit_op (OP_GetElementPtr word_t (wordptr_t, ptr) [(word_t, EXP_Integer i)]).

(* is [v] one of the top-level function names? *)
Definition is_fname (fnames : list var) (v : var) : bool :=
  List.existsb (fun g => Pos.eqb g v) fnames.


Definition gen_operand (fnames : list var) (y : var) : genM (texp typ) :=
  if is_fname fnames y
  then addr <- emit_op (OP_Conversion Ptrtoint wordptr_t
                          (EXP_Ident (ID_Global (var_to_id y))) word_t) ;;
       ret (word_t, addr)
  else ret (var_operand y).

(* store the fields [ys] starting at field-pointer [fieldptr], index [i] *)
Fixpoint store_fields (fnames : list var) (fieldptr : exp typ) (i : Z) (ys : list var) : genM Datatypes.unit :=
  match ys with
  | [] => ret tt
  | y :: ys' =>
      slot <- gen_gep fieldptr i ;;
      v    <- gen_operand fnames y ;;
      gen_store slot v ;;
      store_fields fnames fieldptr (i + 1) ys'
  end.


Fixpoint gen_args (fnames : list var) (ys : list var)
  : genM (list (texp typ * list param_attr)) :=
  match ys with
  | [] => ret []
  | y :: ys' =>
      v    <- gen_operand fnames y ;;
      rest <- gen_args fnames ys' ;;
      ret ((v, @nil param_attr) :: rest)
  end.

(* the callee operand for applying [f] to [nargs] arguments *)
Definition gen_callee (fnames : list var) (f : var) (nargs : nat) : genM (texp typ) :=
  if is_fname fnames f
  then 
    ret (word_t, EXP_Ident (ID_Global (var_to_id f)))
  else (* indirect call: f is an i64 word holding a function pointer *)
    let fnty := TYPE_Function word_t (List.repeat word_t nargs) false in
    fp <- emit_op (OP_Conversion Inttoptr word_t (EXP_Ident (ID_Local (var_to_id f)))
                                 (TYPE_Pointer (Some fnty))) ;;
    ret (word_t, fp).

Definition switch_case (ord : N) (lbl : block_id) : tint_literal * block_id :=
  (TInt_Literal 64%positive (Z.of_N ord), lbl).

(* NOTE: [exp] is qualified as [cps.exp]; importing Vellvm's LLVMAst shadows the
   bare [exp] with the LLVM expression type ([exp : Set -> Set]).
    *)
Fixpoint translate_exp (cenv : ctor_env) (penv : prim_env) (fnames : list var) (e : cps.exp) : genM (terminator typ) :=
  match e with
  | Ehalt x =>
      op <- gen_operand fnames x ;;
      ret (TERM_Ret op)
  | Econstr x t ys e' =>
      rep <- lift_err (get_ctor_rep cenv t) ;;
      match rep with
      | rep_enum ord =>
          (* x := (ord << 1) + 1, materialized as an i64 SSA value *)
          bind_var_op x (OP_IBinop Or word_t (EXP_Integer (enum_immediate ord)) (EXP_Integer 0%Z)) ;;
          translate_exp cenv penv fnames e'
      | rep_boxed ord arity =>
          base     <- gen_alloc ((Z.of_N arity + 1) * 8) ;;               (* header + fields *)
          gen_store base (word_t, EXP_Integer (boxed_header ord arity)) ;; (* header at base[0] *)
          fieldptr <- gen_gep base 1 ;;                                    (* pointer to field 0 *)
          store_fields fnames fieldptr 0 ys ;;
          (* the value word of x is the field pointer, as an integer *)
          bind_var_op x (OP_Conversion Ptrtoint wordptr_t fieldptr word_t) ;;
          translate_exp cenv penv fnames e'
      end
  | Eproj x t n y e' =>
      (* x := y[n]; y is a boxed pointer (points at field 0) *)
      yptr <- emit_op (OP_Conversion Inttoptr word_t (EXP_Ident (ID_Local (var_to_id y))) wordptr_t) ;;
      slot <- gen_gep yptr (Z.of_N n) ;;
      emit (IId (var_to_id x), INSTR_Load word_t (wordptr_t, slot) []) ;;
      translate_exp cenv penv fnames e'
  | Eapp f t ys =>
      (* tail call: %r = call f(ys); ret %r *)
      callee <- gen_callee fnames f (List.length ys) ;;
      args <- gen_args fnames ys ;;
      r <- (id <- fresh_id ;;
            emit (IId id, INSTR_Call callee args []) ;;
            ret (EXP_Ident (ID_Local id))) ;;
      ret (TERM_Ret (word_t, r))
  | Eletapp x f t ys e' =>
      (* non-tail call: %x = call f(ys); continue *)
      callee <- gen_callee fnames f (List.length ys) ;;
      args <- gen_args fnames ys ;;
      emit (IId (var_to_id x), INSTR_Call callee args []) ;;
      translate_exp cenv penv fnames e'
  | Ecase y arms =>
      let fix gen_arms (arms : list (ctor_tag * cps.exp))
          : genM (list (ctor_rep * block_id)) :=
          match arms with
          | [] => ret []
          | (ct, ei) :: rest =>
              rep <- lift_err (get_ctor_rep cenv ct) ;;
              lbl <- fresh_id ;;
              cap <- capture (translate_exp cenv penv fnames ei) ;;
              let '(code, term) := cap in
              emit_block (mk_block lbl [] code term None) ;;
              rest' <- gen_arms rest ;;
              ret ((rep, lbl) :: rest')
          end in
      classified <- gen_arms arms ;;
      let yval := EXP_Ident (ID_Local (var_to_id y)) in
      let unboxed_cases :=
        List.flat_map (fun rl => match rl with
                                 | (rep_enum o, l) => [switch_case o l]
                                 | _ => [] end) classified in
      let boxed_cases :=
        List.flat_map (fun rl => match rl with
                                 | (rep_boxed o _, l) => [switch_case o l]
                                 | _ => [] end) classified in
      ub_lbl  <- fresh_id ;;
      bx_lbl  <- fresh_id ;;
      def_lbl <- fresh_id ;;
      emit_block (mk_block def_lbl [] [] TERM_Unreachable None) ;;
      (* unboxed dispatch: switch on (y >> 1) *)
      ordu <- fresh_id ;;
      emit_block (mk_block ub_lbl []
        [(IId ordu, INSTR_Op (OP_IBinop (LShr false) word_t yval (EXP_Integer 1%Z)))]
        (TERM_Switch (word_t, EXP_Ident (ID_Local ordu)) def_lbl unboxed_cases) None) ;;
      (* boxed dispatch: header at y[-1], switch on (header & 255) *)
      hp    <- fresh_id ;;
      hslot <- fresh_id ;;
      hdr   <- fresh_id ;;
      ordb  <- fresh_id ;;
      emit_block (mk_block bx_lbl []
        [ (IId hp,    INSTR_Op (OP_Conversion Inttoptr word_t yval wordptr_t))
        ; (IId hslot, INSTR_Op (OP_GetElementPtr word_t (wordptr_t, EXP_Ident (ID_Local hp))
                                                 [(word_t, EXP_Integer (-1)%Z)]))
        ; (IId hdr,   INSTR_Load word_t (wordptr_t, EXP_Ident (ID_Local hslot)) [])
        ; (IId ordb,  INSTR_Op (OP_IBinop And word_t (EXP_Ident (ID_Local hdr)) (EXP_Integer 255%Z)))
        ]
        (TERM_Switch (word_t, EXP_Ident (ID_Local ordb)) def_lbl boxed_cases) None) ;;
      (* current block: test low bit, branch to the matching dispatch block *)
      lb  <- fresh_id ;;
      emit (IId lb, INSTR_Op (OP_IBinop And word_t yval (EXP_Integer 1%Z))) ;;
      isu <- fresh_id ;;
      emit (IId isu, INSTR_Op (OP_ICmp Eq word_t (EXP_Ident (ID_Local lb)) (EXP_Integer 1%Z))) ;;
      ret (TERM_Br (TYPE_I 1%positive, EXP_Ident (ID_Local isu)) ub_lbl bx_lbl)
  | Efun _ _ =>
      (* functions are hoisted to the top level; nested Efun should not occur
         (the C backend also rejects it inside a body) *)
      gen_fail "translate_exp: nested Efun (term should be hoisted)"
  | Eprim_val x p e' =>
      match p with
      | existT AstCommon.primInt i =>
          (* unboxed primitive int: x := 2 * to_Z(i) + 1 (same tagging as enum) *)
          bind_var_op x (OP_IBinop Or word_t
                          (EXP_Integer (2 * Uint63.to_Z i + 1)%Z) (EXP_Integer 0%Z)) ;;
          translate_exp cenv penv fnames e'
      | existT AstCommon.primFloat f =>
          (* boxed float: 2 words = header [1277] + the 64-bit pattern; x points
             at field 0 (header at x[-1]), same layout as a boxed constructor. *)
          base     <- gen_alloc (2 * 8) ;;
          gen_store base (word_t, EXP_Integer float_header) ;;
          fieldptr <- gen_gep base 1 ;;
          gen_store fieldptr (word_t, EXP_Integer (float_to_bits f)) ;;
          bind_var_op x (OP_Conversion Ptrtoint wordptr_t fieldptr word_t) ;;
          translate_exp cenv penv fnames e'
      end
  | Eprim x p ys e' =>
      (* apply an external primitive operator, resolved by C name via prim_env *)
      match M.get p penv with
      | None => gen_fail "translate_exp: Eprim primitive id not found in prim_env"
      | Some (_, cname, tinfo, _) =>
          if tinfo
          then gen_fail "translate_exp: Eprim with tinfo unsupported in no-GC backend"
          else
            let callee : texp typ :=
              (word_t, EXP_Ident (ID_Global (Name (bytestring.String.to_string cname)))) in
            args <- gen_args fnames ys ;;
            emit (IId (var_to_id x), INSTR_Call callee args []) ;;
            translate_exp cenv penv fnames e'
      end
  end.

(** ** Assembling functions and the whole program *)

(* run the body translator and wrap the result into a single entry block *)
Definition translate_exp_to_block (cenv : ctor_env) (penv : prim_env) (fnames : list var) (e : cps.exp)
  : error (block typ * list (block typ)) :=
  match translate_exp cenv penv fnames e 0%Z with
  | Err m => Err m
  | Ret (term, code, blks, _) => Ret (mk_block (Name "entry") [] code term None, blks)
  end.

(* a function definition returning i64 and taking params as i64 words *)
Definition mk_fn_def (name : raw_id) (params : list var)
                     (instrs : block typ * list (block typ))
  : definition typ (block typ * list (block typ)) :=
  let argtys := List.map (fun _ => word_t) params in
  {| df_prototype := mk_fun_decl name word_t argtys
   ; df_args      := List.map var_to_id params
   ; df_instrs    := instrs
  |}.

(* the entry point: main () -> i64 *)
Definition mk_main_def (instrs : block typ * list (block typ))
  : definition typ (block typ * list (block typ)) :=
  {| df_prototype := mk_fun_decl (Name "main") word_t []
   ; df_args      := []
   ; df_instrs    := instrs
  |}.

(* translate the top-level function definitions *)
Fixpoint translate_fundefs (cenv : ctor_env) (penv : prim_env) (fnames : list var) (fds : fundefs)
  : error (list (toplevel_entity typ (block typ * list (block typ)))) :=
  match fds with
  | Fnil => Ret []
  | Fcons f t params body fds' =>
      match translate_exp_to_block cenv penv fnames body with
      | Err m => Err m
      | Ret instrs =>
          match translate_fundefs cenv penv fnames fds' with
          | Err m => Err m
          | Ret rest => Ret (TLE_Definition (mk_fn_def (var_to_id f) params instrs) :: rest)
          end
      end
  end.

Definition prim_decls (penv : prim_env)
  : list (toplevel_entity typ (block typ * list (block typ))) :=
  List.map (fun kv =>
              let '(_, (_, cname, _, ar)) := kv in
              TLE_Declaration (mk_fun_decl (Name (bytestring.String.to_string cname))
                                           word_t (List.repeat word_t ar)))
           (M.elements penv).

Definition translate_program (cenv : ctor_env) (penv : prim_env) (prog : cps.exp)
  : error (list (toplevel_entity typ (block typ * list (block typ)))) :=
  let fnames := collect_function_vars prog in
  let externs := TLE_Declaration malloc_decl :: prim_decls penv in
  match prog with
  | Efun fds e =>
      match translate_fundefs cenv penv fnames fds with
      | Err m => Err m
      | Ret fdefs =>
          match translate_exp_to_block cenv penv fnames e with
          | Err m => Err m
          | Ret instrs =>
              Ret (externs ++ fdefs ++ [TLE_Definition (mk_main_def instrs)])%list
          end
      end
  | _ =>
      match translate_exp_to_block cenv penv fnames prog with
      | Err m => Err m
      | Ret instrs =>
          Ret (externs ++ [TLE_Definition (mk_main_def instrs)])%list
      end
  end.




Definition compile_LambdaANF_to_llvm
  (prims : list (kername * string * bool * nat * positive))
  : CertiCoqTrans toplevel.LambdaANF_FullTerm
                  (list (toplevel_entity typ (block typ * list (block typ)))) :=
  fun st =>
    debug_msg "Translating LambdaANF to Vellvm AST" ;;
    _opts <- get_options ;;
    LiftErrorCertiCoqTrans
      "CodegenLLVM(AST)"
      (fun '(env, prog) =>
         let '(_pr, penv, cenv, _ctag, _itag, _nenv, _fenv, _rho) := env in
         match translate_program cenv penv prog with
         | Err msg => compM.Err msg
         | Ret tles => compM.Ret tles
         end)
      st.
