From Coq Require Import ZArith List Sorting.Permutation.
From AUXLib Require Import ListLib.

Definition optimized_selection_sort_result
    (input output : list Z) : Prop :=
  Permutation input output /\ increasing output.
