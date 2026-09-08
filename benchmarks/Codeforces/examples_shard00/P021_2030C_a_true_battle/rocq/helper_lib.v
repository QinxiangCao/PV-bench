
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition NoAdjacentOnesBefore (values : list Z) (upto : Z) : Prop :=
  forall i,
    0 <= i < upto ->
    Znth i values 0 <> 49 \/ Znth (i + 1) values 0 <> 49.
