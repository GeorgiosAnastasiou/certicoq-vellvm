Unset Universe Checking.

From Coq Require Import Strings.String BinNums ZArith.
From ExtLib Require Import Monads.
Import MonadNotation.

From CertiCoq.LambdaANF Require Import cps toplevel.
From CertiCoq.Common    Require Import Common Pipeline_utils.
From MetaCoq.Utils      Require Import MCString.

(* Vellvm AST *)
From Vellvm.Syntax Require Import LLVMAst.
(* Some setups also re-export under Vellvm.LLVMAst; having both is harmless *)
From Vellvm          Require Import LLVMAst.

Open Scope string_scope.
Open Scope monad_scope.
Open Scope Z_scope.

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

(* *)

Definition compile_LambdaANF_to_llvm
  (prims : list (kername * string * bool * nat * positive))
  : CertiCoqTrans toplevel.LambdaANF_FullTerm
                  (list (toplevel_entity typ (block typ * list (block typ)))) :=
  fun st =>
    debug_msg "Translating LambdaANF to Vellvm AST (dummy i32 42)" ;;
    _opts <- get_options ;;
    LiftErrorCertiCoqTrans
      "CodegenLLVM(AST)"
      (fun '(_env, _e) =>
         (* TODO: translate (_env, _e) after dummy compiler *)
         compM.Ret trivial_module_ast)
      st.
