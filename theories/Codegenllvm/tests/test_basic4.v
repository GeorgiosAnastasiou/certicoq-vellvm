Unset Universe Checking.

From Coq Require Import List ZArith Strings.String.
From CertiCoq.LambdaANF Require Import cps toplevel.
From CertiCoq.Common Require Import Common compM.
From CertiCoq.Codegenllvm Require Import LambdaANF_to_llvm.
From Vellvm.QC Require Import ShowAST.
From Vellvm.Syntax Require Import LLVMAst.
Import ListNotations.

Definition mkc (arity ord : N) : ctor_ty_info :=
  Build_ctor_ty_info nAnon nAnon 1%positive arity ord.

Definition cenv : ctor_env :=
  M.set 10%positive (mkc 0 0) (M.empty _).   (* enum ctor, value 1 *)

Definition penv : prim_env := M.empty _.

Definition run (e : cps.exp) : String.string :=
  match translate_program cenv penv e with
  | Ret m => showProg m
  | Err _ => "translate_program returned Err"%string
  end.


Definition t_indirect : cps.exp :=
  Efun
    (Fcons 100%positive 1%positive [101%positive] (Ehalt 101%positive)
      (Fcons 102%positive 1%positive [103%positive]
        (Econstr 104%positive 10%positive []
          (Eapp 103%positive 1%positive [104%positive]))
        Fnil))
    (Eapp 102%positive 1%positive [100%positive]).
Eval vm_compute in (run t_indirect).
