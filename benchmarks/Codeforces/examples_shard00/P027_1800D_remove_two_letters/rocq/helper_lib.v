
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition EqualGapTwoCount (s : list Z) (upto : Z) : Z :=
  #(fun i : Z =>
    0 <= i < upto /\
    Znth i s 0 = Znth (i + 2) s 0).
