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
  M.set 10%positive (mkc 0 0)
 (M.set 11%positive (mkc 2 0)
 (M.set 30%positive (mkc 0 0)
 (M.set 31%positive (mkc 0 1)
 (M.set 40%positive (mkc 0 5)
 (M.set 41%positive (mkc 0 7)
 (M.empty _)))))).

Definition penv : prim_env := M.empty _.

Definition run (e : cps.exp) : String.string :=
  match translate_program cenv penv e with
  | Ret m => showProg m
  | Err _ => "translate_program returned Err"%string
  end.


Definition t_case_unboxed : cps.exp :=
  Econstr 1%positive 31%positive []
    (Ecase 1%positive
      [ (30%positive, Econstr 2%positive 40%positive [] (Ehalt 2%positive))
      ; (31%positive, Econstr 3%positive 41%positive [] (Ehalt 3%positive)) ]).
Eval vm_compute in (run t_case_unboxed).


Definition t_case_boxed : cps.exp :=
  Econstr 1%positive 10%positive []
    (Econstr 2%positive 11%positive [1%positive; 1%positive]
      (Ecase 2%positive
        [ (11%positive, Eproj 3%positive 11%positive 0%N 2%positive (Ehalt 3%positive)) ])).
Eval vm_compute in (run t_case_boxed).


Definition t_fun : cps.exp :=
  Efun (Fcons 5%positive 1%positive [6%positive] (Ehalt 6%positive) Fnil)
    (Econstr 1%positive 10%positive [] (Eapp 5%positive 1%positive [1%positive])).
Eval vm_compute in (run t_fun).
