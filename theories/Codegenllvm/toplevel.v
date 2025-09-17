Unset Universe Checking.

From Coq Require Import List ZArith Strings.String.
From ExtLib Require Import Monads.
Import MonadNotation.

From MetaCoq.Utils Require Import MCString.

From CertiCoq Require Import
  LambdaANF.toplevel
  Common.Common Common.compM Common.Pipeline_utils.

From CertiCoq.Codegenllvm Require Import LambdaANF_to_llvm.

From Vellvm.Syntax Require Import LLVMAst.
From Vellvm.QC Require Import ShowAST DList.

(* --- A small, concrete “module” alias (matches what your pipeline uses) --- *)

Module VellvmMod.
  (* Vellvm “module” = list of toplevel entities *)
  Definition t : Set :=
    list (LLVMAst.toplevel_entity
            LLVMAst.typ
            (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))).
End VellvmMod.

Definition llvm_string (m : VellvmMod.t) : String.string :=
  ShowAST.showProg m.

Definition compile_LambdaANF_to_llvm
  (prims : list (kername * string * bool * nat * positive))
  : CertiCoqTrans toplevel.LambdaANF_FullTerm VellvmMod.t :=
  LambdaANF_to_llvm.compile_LambdaANF_to_llvm prims.
