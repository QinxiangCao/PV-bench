Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition MaximumContainerArea (l : list Z) (ans : Z) : Prop :=
  exists i j,
    0 <= i /\ i < j /\ j < Zlength l /\
    ans = (j - i) * Z.min (Znth i l 0) (Znth j l 0) /\
    forall p q,
      0 <= p -> p < q -> q < Zlength l ->
      (q - p) * Z.min (Znth p l 0) (Znth q l 0) <= ans.

(** Canonical list of the input's [(height,index)] pairs. *)
Definition IndexedHeightsNLogN (l : list Z) : list (Z * Z) :=
  map (fun k : nat => (nth k l 0, Z.of_nat k))
      (seq 0 (length l)).
Definition HeightIndexPermutationNLogN
    (l heights indices : list Z) : Prop :=
  Zlength heights = Zlength l /\
  Zlength indices = Zlength l /\
  Permutation (combine heights indices) (IndexedHeightsNLogN l).
Definition HeightIndexRangeDescendingNLogN
    (heights : list Z) (lo hi : Z) : Prop :=
  0 <= lo /\ lo <= hi /\ hi <= Zlength heights /\
  forall p q,
    lo <= p -> p <= q -> q < hi ->
    Znth q heights 0 <= Znth p heights 0.
Definition SortedHeightIndexWorkspaceNLogN
    (l heights indices : list Z) : Prop :=
  HeightIndexPermutationNLogN l heights indices /\
  HeightIndexRangeDescendingNLogN heights 0 (Zlength heights).

(** Prefix produced while the four caller-owned work arrays are initialized. *)
