Require Export PVbench.Algorithms.container_with_most_water_nlogn.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Require Import SumLib.ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

(** Canonical list of the input's [(height,index)] pairs. *)
Definition IndexedHeightsNLogN (l : list Z) : list (Z * Z) :=
  map (fun k : Z => (Znth k l 0, k)) (Zrange 0 (Zlength l)).


Definition HeightIndexPermutationNLogN
    (l heights indices : list Z) : Prop :=
  Zlength heights = Zlength l /\
  Zlength indices = Zlength l /\
  Permutation (combine heights indices) (IndexedHeightsNLogN l).

Definition HeightIndexRangeDescendingNLogN
    (heights : list Z) (lo hi : Z) : Prop :=
  forall p q,
    lo <= p -> p <= q -> q < hi ->
    Znth q heights 0 <= Znth p heights 0.

Definition SortedHeightIndexWorkspaceNLogN
    (l heights indices : list Z) : Prop :=
  HeightIndexPermutationNLogN l heights indices /\
  HeightIndexRangeDescendingNLogN heights 0 (Zlength heights).

(** Prefix produced while the four caller-owned work arrays are initialized. *)
Definition WorkspacePrefixNLogN
    (l heights indices : list Z) (k : Z) : Prop :=
  Forall2 eq
    (map (fun p => Znth p heights 0) (Zrange 0 k))
    (map (fun p => Znth p l 0) (Zrange 0 k)) /\
  (forall p, 0 <= p < k -> Znth p indices 0 = p).

Definition SameHeightIndexOutsideNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Zlength after_h = Zlength before_h /\
  Zlength after_i = Zlength before_i /\
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun idx => (Znth idx after_h 0, Znth idx after_i 0)) (filter (fun idx => orb (idx <? lo) (hi <=? idx)) (Zrange 0 (Zlength before_h))))
    (map (fun idx => (Znth idx before_h 0, Znth idx before_i 0)) (filter (fun idx => orb (idx <? lo) (hi <=? idx)) (Zrange 0 (Zlength before_h)))).

Definition HeightIndexRangePermutationNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Permutation
    (combine (sublist lo hi after_h) (sublist lo hi after_i))
    (combine (sublist lo hi before_h) (sublist lo hi before_i)).

(** Mathematical result of sorting one half-open range. *)
Definition HeightIndexRangeSortResultNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Zlength before_h = Zlength before_i /\
  Zlength after_h = Zlength after_i /\
  SameHeightIndexOutsideNLogN
    before_h before_i after_h after_i lo hi /\
  HeightIndexRangePermutationNLogN
    before_h before_i after_h after_i lo hi /\
  HeightIndexRangeDescendingNLogN after_h lo hi.

(** State of a standard merge of two descending source ranges.  It says that
    the destination prefix contains exactly the consumed source pairs, is
    descending, and dominates every still-pending height. *)
Definition MergePrefixStateNLogN
    (source_h source_i dest0_h dest0_i dest_h dest_i : list Z)
    (left middle right p q output : Z) : Prop :=
  HeightIndexRangeDescendingNLogN source_h left middle /\
  HeightIndexRangeDescendingNLogN source_h middle right /\
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun idx => (Znth idx dest_h 0, Znth idx dest_i 0)) (filter (fun idx => orb (idx <? left) (output <=? idx)) (Zrange 0 (Zlength dest0_h))))
    (map (fun idx => (Znth idx dest0_h 0, Znth idx dest0_i 0)) (filter (fun idx => orb (idx <? left) (output <=? idx)) (Zrange 0 (Zlength dest0_h)))) /\
  Permutation
    (combine (sublist left output dest_h) (sublist left output dest_i))
    (combine (sublist left p source_h) (sublist left p source_i) ++
     combine (sublist middle q source_h) (sublist middle q source_i)) /\
  (forall u v,
     left <= u -> u <= v -> v < output ->
     Znth v dest_h 0 <= Znth u dest_h 0) /\
  (forall u v,
     left <= u < output ->
     ((p <= v < middle) \/ (q <= v < right)) ->
     Znth v source_h 0 <= Znth u dest_h 0).

Definition HeightIndexRangeMergeResultNLogN
    (source_h source_i dest0_h dest0_i dest_h dest_i : list Z)
    (left middle right : Z) : Prop :=
  SameHeightIndexOutsideNLogN
    dest0_h dest0_i dest_h dest_i left right /\
  Permutation
    (combine (sublist left right dest_h) (sublist left right dest_i))
    (combine (sublist left right source_h) (sublist left right source_i)) /\
  HeightIndexRangeDescendingNLogN dest_h left right.

(** State while copying a merged range from the buffer back to the work
    arrays. *)
Definition CopyHeightIndexPrefixNLogN
    (source_h source_i dest0_h dest0_i dest_h dest_i : list Z)
    (left right k : Z) : Prop :=
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun p => (Znth p dest_h 0, Znth p dest_i 0)) (Zrange left k))
    (map (fun p => (Znth p source_h 0, Znth p source_i 0)) (Zrange left k)) /\
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun idx => (Znth idx dest_h 0, Znth idx dest_i 0)) (filter (fun idx => orb (idx <? left) (k <=? idx)) (Zrange 0 (Zlength dest0_h))))
    (map (fun idx => (Znth idx dest0_h 0, Znth idx dest0_i 0)) (filter (fun idx => orb (idx <? left) (k <=? idx)) (Zrange 0 (Zlength dest0_h)))).


(** Endpoints of the original indices represented by a nonempty sorted
    prefix.  These endpoints are sufficient to find the farthest prior bar. *)
Definition ProcessedIndexEndpointsNLogN
    (indices : list Z) (k minimum maximum : Z) : Prop :=
  min_value_of_subset Z.le (fun p : Z => 0 <= p < k)
    (fun p => Znth p indices 0) minimum /\
  max_value_of_subset Z.le (fun p : Z => 0 <= p < k)
    (fun p => Znth p indices 0) maximum.


Definition ProcessedContainerPairNLogN
    (l indices : list Z) (k : Z) (ij : Z * Z) : Prop :=
  ContainerPairNLogN l (fst ij) (snd ij) /\
  In (fst ij) (sublist 0 k indices) /\
  In (snd ij) (sublist 0 k indices).

Definition ProcessedContainerMaximumNLogN
    (l indices : list Z) (k ans : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (ProcessedContainerPairNLogN l indices k)
    (fun ij : Z * Z =>
       ContainerAreaNLogN l (fst ij) (snd ij))
    0 ans.
