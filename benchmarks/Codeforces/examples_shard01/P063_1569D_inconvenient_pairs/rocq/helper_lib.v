Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SumLib.ZRect.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P063_1569D_inconvenient_pairs.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* Mathematical interfaces used by the normalized implementation.  They
   describe the order, the selected street strips, and the finite pair sets;
   none of them executes the C loops. *)
Definition StripIndex (streets : list Z) (v r : Z) : Prop :=
  (r = -1 /\ In v streets) \/
  (0 <= r < Zlength streets - 1 /\
   Znth r streets 0 < v < Znth (r + 1) streets 0).

Definition ItemLe (a b : Z * Z) : Prop :=
  fst a < fst b \/ (fst a = fst b /\ snd a <= snd b).

Definition ItemLe4 (g1 k1 g2 k2 : Z) : Prop :=
  g1 < g2 \/ (g1 = g2 /\ k1 <= k2).

Definition ParallelPermutation
    (groups keys groups' keys' : list Z) : Prop :=
  Permutation (combine groups keys) (combine groups' keys').

Definition ItemsIncreasing (groups keys : list Z) : Prop :=
  Zlength groups = Zlength keys /\
  forall i j, 0 <= i /\ i <= j /\ j < Zlength groups ->
    ItemLe (Znth i (combine groups keys) (0, 0))
           (Znth j (combine groups keys) (0, 0)).

Definition HeapParentsFromItems
    (groups keys : list Z) (lo hi : Z) : Prop :=
  forall child,
    1 <= child <= hi -> lo <= (child - 1) / 2 ->
    ItemLe (Znth child (combine groups keys) (0, 0))
           (Znth ((child - 1) / 2) (combine groups keys) (0, 0)).

Definition HeapOrderedExceptAtFromItems
    (groups keys : list Z) (lo hi bad : Z) : Prop :=
  forall child,
    1 <= child <= hi -> lo <= (child - 1) / 2 ->
    (child - 1) / 2 <> bad ->
    ItemLe (Znth child (combine groups keys) (0, 0))
           (Znth ((child - 1) / 2) (combine groups keys) (0, 0)).

Definition SelectedLargerChildItems
    (groups keys : list Z) (root hi child : Z) : Prop :=
  (child = 2 * root + 1 \/ child = 2 * root + 2) /\ child <= hi /\
  (2 * root + 1 <= hi ->
     ItemLe (Znth (2 * root + 1) (combine groups keys) (0, 0))
            (Znth child (combine groups keys) (0, 0))) /\
  (2 * root + 2 <= hi ->
     ItemLe (Znth (2 * root + 2) (combine groups keys) (0, 0))
            (Znth child (combine groups keys) (0, 0))).

Definition HeapSortItemsState
    (groups0 keys0 groups keys : list Z) (hi : Z) : Prop :=
  Zlength groups = Zlength groups0 /\ Zlength keys = Zlength keys0 /\
  ParallelPermutation groups0 keys0 groups keys /\
  HeapParentsFromItems groups keys 0 hi /\
  ItemsIncreasing (sublist (hi + 1) (Zlength groups) groups)
                  (sublist (hi + 1) (Zlength keys) keys) /\
  (forall p q, 0 <= p <= hi -> hi < q < Zlength groups ->
     ItemLe (Znth p (combine groups keys) (0, 0))
            (Znth q (combine groups keys) (0, 0))).

Definition PairCountPrefix (groups keys : list Z) (hi out : Z) : Prop :=
  out = #(fun ij : Z * Z =>
            0 <= fst ij < hi /\ 0 <= snd ij < hi /\ fst ij < snd ij /\
            Znth (fst ij) groups 0 = Znth (snd ij) groups 0 /\
            Znth (fst ij) keys 0 <> Znth (snd ij) keys 0).

Definition SameKeyCountRange (keys : list Z) (lo hi : Z) : Z :=
  #(fun ij : Z * Z =>
      lo <= fst ij < hi /\ lo <= snd ij < hi /\ fst ij < snd ij /\
      Znth (fst ij) keys 0 = Znth (snd ij) keys 0).

Definition CountGroupPhase
    (groups keys : list Z) (i j p total : Z) : Prop :=
  exists before,
    PairCountPrefix groups keys i before /\
    total = before + (j - i) * (j - i - 1) / 2 -
                     SameKeyCountRange keys i p.

Definition SameValueRange (l : list Z) (lo hi : Z) : Prop :=
  forall q, lo <= q < hi -> Znth q l 0 = Znth lo l 0.

Definition VerticalEntry (xs ys : list Z) (person : Z * Z)
    (group key : Z) : Prop :=
  StripIndex ys (snd person) group /\ 0 <= group /\ key = fst person.

Definition HorizontalEntry (xs ys : list Z) (person : Z * Z)
    (group key : Z) : Prop :=
  StripIndex ys (snd person) (-1) /\
  StripIndex xs (fst person) group /\ 0 <= group /\ key = snd person.

Definition EnumeratesEntries
    (Entry : (Z * Z) -> Z -> Z -> Prop)
    (people : list (Z * Z)) (done : Z) (groups keys : list Z) : Prop :=
  exists indices : list Z,
    Zlength indices = Zlength groups /\
    Zlength groups = Zlength keys /\ mono_inc indices /\
    (forall t, 0 <= t < Zlength indices ->
       0 <= Znth t indices 0 < done /\
       Entry (Znth (Znth t indices 0) people (0, 0))
             (Znth t groups 0) (Znth t keys 0)) /\
    (forall q, 0 <= q < done ->
       (exists group key,
          Entry (Znth q people (0, 0)) group key) -> In q indices).

Definition ClassifiedPrefix
    (xs ys : list Z) (people : list (Z * Z)) (done : Z)
    (vg vk hg hk : list Z) : Prop :=
  EnumeratesEntries (VerticalEntry xs ys) people done vg vk /\
  EnumeratesEntries (HorizontalEntry xs ys) people done hg hk.

Definition ClassifiedPairCounts
    (xs ys : list Z) (people : list (Z * Z))
    (vg vk hg hk : list Z) (out : Z) : Prop :=
  ClassifiedPrefix xs ys people (Zlength people) vg vk hg hk /\
  exists vertical horizontal,
    PairCountPrefix vg vk (Zlength vg) vertical /\
    PairCountPrefix hg hk (Zlength hg) horizontal /\
    out = vertical + horizontal.

Definition StreetCoordinateBounds (streets : list Z) : Prop :=
  forall i, 0 <= i < Zlength streets -> 0 <= Znth i streets 0 <= 1000000.

Definition PeopleCoordinateBounds (people : list (Z * Z)) : Prop :=
  forall i, 0 <= i < Zlength people ->
    0 <= fst (Znth i people (0, 0)) <= 1000000 /\
    0 <= snd (Znth i people (0, 0)) <= 1000000.

(* Stable boundary facts used by the normalized heap and run scans. *)
Definition SiftChildrenBelowParentItems
    (groups keys : list Z) (start hi root : Z) : Prop :=
  root = start \/
  forall child,
    (child = 2 * root + 1 \/ child = 2 * root + 2) -> child <= hi ->
    ItemLe (Znth child (combine groups keys) (0, 0))
           (Znth ((root - 1) / 2) (combine groups keys) (0, 0)).

Definition ValueRunBoundary (l : list Z) (i : Z) : Prop :=
  i = 0 \/ i = Zlength l \/
  (0 < i < Zlength l /\ Znth (i - 1) l 0 <> Znth i l 0).

Definition RangeRunBoundary (l : list Z) (lo hi p : Z) : Prop :=
  p = lo \/ p = hi \/
  (lo < p < hi /\ Znth (p - 1) l 0 <> Znth p l 0).

(* A semantic, implementation-independent correspondence for a processed prefix:
   counting the two normalized entry lists gives exactly the inconvenient pairs
   whose two people lie in that prefix. *)
Definition ClassifiedCountsCorrect
    (xs ys : list Z) (people : list (Z * Z)) (done : Z)
    (vg vk hg hk : list Z) : Prop :=
  forall vertical horizontal,
    PairCountPrefix vg vk (Zlength vg) vertical ->
    PairCountPrefix hg hk (Zlength hg) horizontal ->
    vertical + horizontal =
      #(fun ij : Z * Z =>
          0 <= fst ij < done /\
          0 <= snd ij < done /\
          fst ij < snd ij /\
          Inconvenient xs ys
            (Znth (fst ij) people (0, 0))
            (Znth (snd ij) people (0, 0))).

(* The stable part of a heap-extraction state.  The prefix may be permuted by
   sifting, while the suffix remains sorted and above every prefix item. *)
Definition ExtractionFrameItems
    (groups keys : list Z) (split : Z) : Prop :=
  ItemsIncreasing (sublist split (Zlength groups) groups)
                  (sublist split (Zlength keys) keys) /\
  (forall p q,
      0 <= p < split -> split <= q < Zlength groups ->
      ItemLe (Znth p (combine groups keys) (0, 0))
             (Znth q (combine groups keys) (0, 0))).
