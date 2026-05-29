Unset Universe Checking.

From Coq Require Import List ZArith Strings.String Floats.
From CertiCoq.LambdaANF Require Import cps toplevel.
From CertiCoq.Common Require Import Common compM AstCommon.
From CertiCoq.Codegenllvm Require Import LambdaANF_to_llvm.
From Vellvm.QC Require Import ShowAST.
From Vellvm.Syntax Require Import LLVMAst.
Import ListNotations.

Definition cenv : ctor_env := M.empty _.   (* unused: Eproj/Eprim_val need no ctor info *)
Definition penv : prim_env := M.empty _.

Definition run (e : cps.exp) : String.string :=
  match translate_program cenv penv e with
  | Ret m => showProg m
  | Err _ => "translate_program returned Err"%string
  end.

Eval vm_compute in (float_to_bits 1.5%float).

Definition t_float : cps.exp :=
  Eprim_val 1%positive (existT AstCommon.prim_value AstCommon.primFloat 1.5%float)
    (Eproj 2%positive 1%positive 0%N 1%positive
      (Ehalt 2%positive)).
Eval vm_compute in (run t_float).
