Unset Universe Checking.
From Coq Require Import Strings.String BinNums ZArith.
From ExtLib Require Import Monads.
Import MonadNotation.

From CertiCoq.LambdaANF Require Import cps.
From CertiCoq.Common Require Import Common Pipeline_utils.
From MetaCoq.Utils Require Import MCString.
From CertiCoq.LambdaANF Require Import toplevel.

From Vellvm Require Import LLVMAst.
From Vellvm.QC  Require Import ShowAST.

Open Scope string_scope.
Open Scope monad_scope.
Open Scope Z_scope.

(* vellvm AST that defines @main returning i32 42 --- *)
Definition i32_42 : texp typ := (TYPE_I 32%positive, EXP_Integer 42%Z).

Definition ret_block : block typ :=
  mk_block (Name "entry") [] [] (TERM_Ret i32_42) None.

Definition main_decl : declaration typ :=
  mk_declaration (Name "main")
                 (TYPE_Function (TYPE_I 32%positive) [] false)
                 ([],[]) [] [].

Definition main_def : definition typ (block typ * list (block typ)) :=
  {| df_prototype := main_decl; df_args := []; df_instrs := (ret_block, []) |}.

Definition trivial_module_ast
  : list (toplevel_entity typ (block typ * list (block typ))) :=
  [ TLE_Definition main_def ].

(* backend entry point used by the pipeline *)
Definition compile_LambdaANF_to_llvm
  (prims : list (kername * MCString.string * bool * nat * positive))
  : CertiCoqTrans toplevel.LambdaANF_FullTerm
                  (list (toplevel_entity typ (block typ * list (block typ)))) :=
  fun st =>
    debug_msg "Translating LambdaANF to Vellvm AST" ;;
    _opts <- get_options ;;
    LiftErrorCertiCoqTrans
      "CodegenLLVM"
      (fun '(env, e) =>
         (* env:
            let '(pr, prims_env, cenv, ctag, itag, nenv, fenv, rho) := env in ... *)
         compM.Ret trivial_module_ast)
      st.
