Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P086_639D_bear_and_contribution.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition ZSum (l : list Z) : Z := fold_right Z.add 0 l.

(* Array-embedded binary max-heap: index arithmetic follows C's [(i-1)/2],
   which the generated goals read as [Z.quot]. *)

Definition HeapParent (child : Z) : Z := Z.quot (child - 1) 2.

(* Every parent/child edge whose parent index is at least [lo] is ordered.
   [lo = 0] is a full max-heap; [lo = root + 1] is the state in which only
   the subtrees strictly below [root] are known to be heaps, which is the
   precondition both sift-down callers establish. *)

Definition HeapOrderedFrom (l : list Z) (size lo : Z) : Prop :=
  forall child,
    0 < child ->
    child < size ->
    lo <= HeapParent child ->
    Znth (HeapParent child) l 0 >= Znth child l 0.

Definition HeapOrdered (l : list Z) (size : Z) : Prop :=
  HeapOrderedFrom l size 0.

(* Two parallel arrays abstracted as one list of pairs.  Permuting the two
   arrays independently would be unsound, so the sort contract is stated on
   the zipped list.  [combine] truncates at the shorter argument, hence the
   explicit length conjuncts. *)

Definition ZipPerm (t0 b0 t1 b1 : list Z) : Prop :=
  Zlength b0 = Zlength t0 /\
  Zlength t1 = Zlength t0 /\
  Zlength b1 = Zlength t0 /\
  Permutation (combine t0 b0) (combine t1 b1).

Definition Nondecreasing (l : list Z) : Prop :=
  forall i j,
    0 <= i ->
    i <= j ->
    j < Zlength l ->
    Znth i l 0 <= Znth j l 0.

(* ------------------------------------------------------------------ *)
(* Internal (body-only) declarations.                                  *)
(* ------------------------------------------------------------------ *)

(* --- hpush: sift-up ------------------------------------------------ *)

Definition HeapOrderExceptUp (l : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node -> node < size -> node <> child ->
    Znth (HeapParent node) l 0 >= Znth node l 0.

Definition PushHoleGuard (l : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node -> node < size -> HeapParent node = child ->
    Znth (HeapParent child) l 0 >= Znth node l 0.

Definition PushSiftState (l cur : list Z) (size child x : Z) : Prop :=
  Zlength cur = Zlength l /\
  Znth child cur 0 = x /\
  Permutation (sublist 0 (size + 1) cur) (x :: sublist 0 size l) /\
  HeapOrderExceptUp cur (size + 1) child /\
  PushHoleGuard cur (size + 1) child.

(* --- hpop: sift-down ----------------------------------------------- *)

Definition HeapOrderExceptDown (l : list Z) (size index : Z) : Prop :=
  forall child,
    0 < child -> child < size -> HeapParent child <> index ->
    Znth (HeapParent child) l 0 >= Znth child l 0.

Definition PopHoleGuard (l : list Z) (size index : Z) : Prop :=
  index = 0 \/
  (forall child,
     0 < child -> child < size -> HeapParent child = index ->
     Znth (HeapParent index) l 0 >= Znth child l 0).

Definition PopSiftState (l cur : list Z) (size index : Z) : Prop :=
  Zlength cur = Zlength l /\
  Permutation (sublist 0 (size - 1) cur) (sublist 1 size l) /\
  HeapOrderExceptDown cur (size - 1) index /\
  PopHoleGuard cur (size - 1) index.

(* --- sift_candidates: sift-down on zipped pairs --------------------- *)

Definition SiftState (t0 b0 t b : list Z) (size lo index : Z) : Prop :=
  ZipPerm t0 b0 t b /\
  sublist size (Zlength t0) t = sublist size (Zlength t0) t0 /\
  sublist size (Zlength b0) b = sublist size (Zlength b0) b0 /\
  (forall child,
     0 < child -> child < size -> lo <= HeapParent child ->
     HeapParent child <> index ->
     Znth (HeapParent child) t 0 >= Znth child t 0) /\
  (index = lo \/
   (forall child,
      0 < child -> child < size -> HeapParent child = index ->
      Znth (HeapParent index) t 0 >= Znth child t 0)).

(* --- sort_candidates: extraction phase ------------------------------ *)

Definition HeapSortState (t : list Z) (n hi : Z) : Prop :=
  Nondecreasing (sublist (hi + 1) n t) /\
  (forall p q,
     0 <= p -> p <= hi -> hi < q -> q < n ->
     Znth p t 0 <= Znth q t 0).

(* --- solver: shift and candidate normalisation ---------------------- *)

Definition ShiftedPrefix (values sh : list Z) (cnt : Z) : Prop :=
  forall i, 0 <= i < cnt -> Znth i sh 0 = Znth i values 0 + 2000000000.

(* Marginal price of one further block of five. *)

Definition WCost (b c : Z) : Z := Z.min b (5 * c).

(* Least value congruent to [j] mod 5 that is at least [s]. *)

Definition TargetPoint (s j : Z) : Z := s + (j - s) mod 5.

(* The part of blogger [s]'s raise cost that does not depend on the target. *)

Definition NormalizedBase (s j W c : Z) : Z :=
  ((j - s) mod 5) * c - ((TargetPoint s j - j) / 5) * W.

Definition CandPrefix (sh : list Z) (j W c cnt : Z) (t b : list Z) : Prop :=
  forall i, 0 <= i < cnt ->
    Znth i t 0 = TargetPoint (Znth i sh 0) j /\
    Znth i b 0 = NormalizedBase (Znth i sh 0) j W c.

(* --- solver: the k smallest bases ----------------------------------- *)

Definition SubMultiset (m l : list Z) : Prop :=
  exists rest, Permutation l (m ++ rest).

Definition MinSubMultiset (l m : list Z) : Prop :=
  SubMultiset m l /\
  (forall m',
     SubMultiset m' l -> Zlength m' = Zlength m -> ZSum m <= ZSum m').

Definition KSmallSum (l : list Z) (k s : Z) : Prop :=
  exists m, MinSubMultiset l m /\ Zlength m = k /\ s = ZSum m.

Definition HeapContent (sb : list Z) (i : Z) (H : list Z) (hsum : Z) : Prop :=
  MinSubMultiset (sublist 0 i sb) H /\ hsum = ZSum H.

(* --- solver: residue classes, the sweep and the running best -------- *)

Definition TieCostAtResidue (values : list Z) (k b c j cost : Z) : Prop :=
  exists (chosen costs : list Z) (target : Z),
    target mod 5 = j /\
    ChosenBloggers values k chosen /\
    Zlength costs = k /\
    (forall i, 0 <= i < k ->
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) /\
    cost = fold_right Z.add 0 costs.

Definition SweepValue (st sb : list Z) (k j W i v : Z) : Prop :=
  exists s,
    KSmallSum (sublist 0 (i + 1) sb) k s /\
    v = s + k * ((Znth i st 0 - j) / 5) * W.

Definition BestState (P : Z -> Prop) (best : Z) : Prop :=
  (best = -1 /\ forall v, ~ P v) \/
  (0 <= best /\ min_value_of_subset Z.le P (fun x => x) best).

Definition ResidueBest (values : list Z) (k b c j best : Z) : Prop :=
  BestState
    (fun v => exists j', 0 <= j' < j /\ TieCostAtResidue values k b c j' v)
    best.

Definition SweepSet
    (values : list Z) (k b c j : Z) (st sb : list Z) (W i : Z) (v : Z) : Prop :=
  (exists j', 0 <= j' < j /\ TieCostAtResidue values k b c j' v) \/
  (exists i', k - 1 <= i' /\ i' < i /\ SweepValue st sb k j W i' v).

Definition SweepBest
    (values : list Z) (k b c j : Z) (st sb : list Z) (W i best : Z) : Prop :=
  BestState (SweepSet values k b c j st sb W i) best.
