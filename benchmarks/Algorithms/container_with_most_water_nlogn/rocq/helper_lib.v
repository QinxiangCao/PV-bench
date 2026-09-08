Require Import PVbench.Algorithms.container_with_most_water_nlogn.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition ContainerHeightNLogN (l : list Z) (i j : Z) : Z :=
  Z.min (Znth i l 0) (Znth j l 0).
Definition ContainerAreaNLogN (l : list Z) (i j : Z) : Z :=
  (j - i) * ContainerHeightNLogN l i j.
Definition ContainerPairNLogN (l : list Z) (i j : Z) : Prop :=
  0 <= i /\ i < j /\ j < Zlength l.

(** The exact attained global optimum, stated only in terms of original
    indices.  A different implementation can satisfy the same predicate. *)
Definition WorkspacePrefixNLogN
    (l heights indices : list Z) (k : Z) : Prop :=
  (forall p, 0 <= p < k -> Znth p heights 0 = Znth p l 0) /\
  (forall p, 0 <= p < k -> Znth p indices 0 = p).
Definition SameHeightIndexOutsideNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Zlength after_h = Zlength before_h /\
  Zlength after_i = Zlength before_i /\
  forall k,
    0 <= k < Zlength before_h ->
    (k < lo \/ hi <= k) ->
    Znth k after_h 0 = Znth k before_h 0 /\
    Znth k after_i 0 = Znth k before_i 0.
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
  0 <= lo /\ lo <= hi /\ hi <= Zlength before_h /\
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
  (forall t,
     0 <= t < Zlength dest0_h ->
     (t < left \/ output <= t) ->
     Znth t dest_h 0 = Znth t dest0_h 0 /\
     Znth t dest_i 0 = Znth t dest0_i 0) /\
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
  0 <= left /\ left <= middle /\ middle <= right /\
  right <= Zlength source_h /\
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
  (forall p, left <= p < k ->
     Znth p dest_h 0 = Znth p source_h 0 /\
     Znth p dest_i 0 = Znth p source_i 0) /\
  (forall p,
     0 <= p < Zlength dest0_h ->
     (p < left \/ k <= p) ->
     Znth p dest_h 0 = Znth p dest0_h 0 /\
     Znth p dest_i 0 = Znth p dest0_i 0).

(** Endpoints of the original indices represented by a nonempty sorted
    prefix.  These endpoints are sufficient to find the farthest prior bar. *)
Definition ProcessedIndexEndpointsNLogN
    (indices : list Z) (k minimum maximum : Z) : Prop :=
  (exists p, 0 <= p < k /\ Znth p indices 0 = minimum) /\
  (exists p, 0 <= p < k /\ Znth p indices 0 = maximum) /\
  (forall p, 0 <= p < k ->
     minimum <= Znth p indices 0 <= maximum).
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
