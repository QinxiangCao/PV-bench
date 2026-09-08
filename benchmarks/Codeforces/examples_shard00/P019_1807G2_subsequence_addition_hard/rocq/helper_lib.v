
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition PrefixAdditionState
    (sorted : list Z) (processed total : Z) : Prop :=
  1 <= processed <= Zlength sorted /\
  total = ListLib.sum (sublist 0 processed sorted) /\
  Znth 0 sorted 0 = 1 /\
  forall i,
    1 <= i < processed ->
    Znth i sorted 0 <= ListLib.sum (sublist 0 i sorted).
