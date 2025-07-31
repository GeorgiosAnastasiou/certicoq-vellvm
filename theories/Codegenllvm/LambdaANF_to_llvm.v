(** * Trivial LambdaANF to LLVM Backend 
    This backend ignores the input LambdaANF expression and always returns "42". *)

Unset Universe Checking.
Require Import Coq.Strings.String.
From CertiCoq.LambdaANF Require Import cps cps_util.
From CertiCoq.Common Require Import Pipeline_utils.  (* Provides name_env, ctor_env, prim_env, error monad etc. *)
From ExtLib Require Import Monads.

(* Import MonadNotation. *)
(* For using monadic notation like 'ret' if available. *) 


(* From CertiCoq Require Import LambdaANF.toplevel.
   ---
   not used anymore *)

(* expects 
CertiCoq.LambdaANF.cps.exp  :  Set 
i think
 *)
From Vellvm.Syntax Require Import LLVMAst.
From Vellvm.QC Require Import ShowAST. (* pretty printer *)
From CertiCoq.Common Require Import Common.
Require Import LambdaANF.toplevel. 

From ExtLib.Structures Require Import Monad.
Import MonadNotation. 
Open Scope string_scope.
Open Scope monad_scope. 


Locate error.
Print error. 

From Coq Require Import BinNums ZArith.
Open Scope N_scope. 
Open Scope Z_scope.
From QuickChick Require Import Show.

Definition i32_42 : texp typ :=
  (TYPE_I 32%N , EXP_Integer 42%Z).

Print i32_42. 

Definition ret_block : block typ :=
  mk_block (Name "entry") [] [] (TERM_Ret i32_42) None.

Definition main_decl : declaration typ :=
  mk_declaration
      (Name "main")
      (TYPE_Function (TYPE_I 32) [] false)  (* i32 @main() *)
      ([],[]) [] [].

About mk_definition.

Definition main_def : definition typ (block typ * list (block typ)) :=
  {|
    df_prototype := main_decl ;
    df_args      := [] ;
    df_instrs    := (ret_block, [])
  |}.

About toplevel_entities.
(* 
   Set (the value-type used in the program) 
-> Set(the type of function body) 
-> Set (result)
  *)

Definition trivial_module
  : @toplevel_entities typ (block typ * list (block typ)) :=
  [ TLE_Definition main_def ].
(* ─── Backend entry point used by the pipeline ───────────────────── *)

Compute (show trivial_module).

Definition LambdaANF_to_llvm
           (_nenv : name_env) (_cenv : ctor_env) (_penv : prim_env)
           (_e    : cps.exp)
           (*: compM.error string := *)
           (* : exception String.string :=  *)
  : compM.error String.string := 
  compM.Ret (show trivial_module).


About show.



About dshow.
(**  The CertiCoq LambdaANF pipeline returns a 7-tuple
     (pr, cenv, penv, nenv, fenv, <something>, e).      *)


(* 
(pr_env,          (* primitive environment *)
 cenv,            (* constructor environment *)
 ctag,            (* ctor tag generator *)
 itag,            (* ind tag generator *)
 nenv,            (* name environment *)
 fenv,            (* fun info environment *)
 _,               (* some internal flag *)
 prog : cps.exp)  (* the ANF term itself *)
 *)




 



Definition compile_llvm
           (prims : list (kername * string * bool * nat * positive))
  : CertiCoqTrans toplevel.LambdaANF_FullTerm String.string :=
  fun st =>
    debug_msg "Translating from LambdaANF to LLVM IR" ;;
    _opts <- get_options ;;

    LiftErrorCertiCoqTrans
      "CodegenLLVM"
      (fun '( _       
           , penv     
           , cenv     
           , _ctag    
           , _itag
           , nenv     
           , _fenv
           , _extra
           , e        
           ) =>
         LambdaANF_to_llvm nenv cenv penv e)
      st.



