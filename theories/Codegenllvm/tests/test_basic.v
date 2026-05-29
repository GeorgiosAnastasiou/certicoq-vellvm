Unset Universe Checking.

From Coq Require Import List ZArith Strings.String.
From CertiCoq.LambdaANF Require Import cps toplevel.
From CertiCoq.Common Require Import Common compM.
From CertiCoq.Codegenllvm Require Import LambdaANF_to_llvm.
From Vellvm.QC Require Import ShowAST.
From Vellvm.Syntax Require Import LLVMAst.
Import ListNotations.


Definition cenv : ctor_env :=
  M.set 10%positive (Build_ctor_ty_info nAnon nAnon 1%positive 0%N 0%N)
 (M.set 11%positive (Build_ctor_ty_info nAnon nAnon 1%positive 2%N 0%N)
 (M.empty _)).

Definition penv : prim_env := M.empty _.


Definition run (e : cps.exp) : String.string :=
  match translate_program cenv penv e with
  | Ret m => showProg m
  | Err _ => "translate_program returned Err"%string
  end.


Definition t_enum : cps.exp :=
  Econstr 1%positive 10%positive [] (Ehalt 1%positive).
Eval vm_compute in (run t_enum).

Definition t_boxed : cps.exp :=
  Econstr 1%positive 10%positive []
    (Econstr 2%positive 11%positive [1%positive; 1%positive]
      (Eproj 3%positive 11%positive 0%N 2%positive
        (Ehalt 3%positive))).
Eval vm_compute in (run t_boxed).
