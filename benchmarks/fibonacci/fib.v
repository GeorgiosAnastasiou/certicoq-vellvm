From Coq Require Import Uint63 ZArith.

Open Scope uint63_scope.

(* nat-iterative Fibonacci *)
Fixpoint fib_loop_nat (i a b : nat) : nat :=
  match i with
  | 0%nat => b
  | S i'  => fib_loop_nat i' (a + b)%nat a
  end.

Definition fib_nat (n : nat) : nat :=
  fib_loop_nat n 1%nat 0%nat.

Definition int_to_nat (x : int) : nat :=
  Z.to_nat (Uint63.to_Z x).

Definition nat_to_int (n : nat) : int :=
  Uint63.of_Z (Z.of_nat n).

Definition fib63 (n : int) : int :=
  nat_to_int (fib_nat (int_to_nat n)).

Definition program : int := fib63 45%uint63.

From CertiCoq.Plugin Require Import CertiCoq.
(* CertiCoq Compile program.*)

(* CertiCoq Run -build_dir "extraction" program. *)

CertiCoq Compile -build_dir "extraction" program.

(* CertiCoq Compile -config 1 -0 1 -ext "_fib1" program. *)

CertiCoq Generate Glue -file "glue_fib" [ nat ].
