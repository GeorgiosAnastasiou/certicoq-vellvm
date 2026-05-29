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
 (M.set 31%positive (mkc 0 1)
 (M.set 11%positive (mkc 2 0)
 (M.set 12%positive (mkc 1 0)
 (M.empty _)))).

Definition penv : prim_env := M.empty _.

Definition run (e : cps.exp) : String.string :=
  match translate_program cenv penv e with
  | Ret m => showProg m
  | Err _ => "translate_program returned Err"%string
  end.


Definition t_field1 : cps.exp :=
  Econstr 1%positive 10%positive []
    (Econstr 2%positive 31%positive []
      (Econstr 3%positive 11%positive [1%positive; 2%positive]
        (Eproj 4%positive 11%positive 1%N 3%positive
          (Ehalt 4%positive)))).
Eval vm_compute in (run t_field1).


Definition t_nested : cps.exp :=
  Econstr 1%positive 10%positive []
    (Econstr 2%positive 31%positive []
      (Econstr 3%positive 11%positive [1%positive; 2%positive]
        (Econstr 4%positive 12%positive [3%positive]
          (Eproj 5%positive 12%positive 0%N 4%positive
            (Eproj 6%positive 11%positive 1%N 5%positive
              (Ehalt 6%positive)))))).
Eval vm_compute in (run t_nested).
