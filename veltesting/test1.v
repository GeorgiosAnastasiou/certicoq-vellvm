From CertiCoq.Plugin Require Import CertiCoq.


Definition forty_two := 42.
(* Redirect "forty_two.ll" (CertiCoq Compile llvm forty_two). *)

CertiCoq Compile llvm forty_two.
