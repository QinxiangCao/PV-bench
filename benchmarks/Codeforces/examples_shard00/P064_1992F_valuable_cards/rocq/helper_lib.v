Require Export PVbench.Codeforces.examples_shard00.P064_1992F_valuable_cards.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** A direct mathematical description of the products represented by the
    program's divisor table.  This deliberately reuses the same finite choice
    of indices as [BadCardSegment], so later bridge lemmas do not need a second
    encoding of subsequences. *)
Definition SelectedProduct (seg : list Z) (ids : Z -> Prop) : Z :=
  fold_right Z.mul 1
    (map (fun i => Znth i seg 0)
      (@enum Z (fun i => 0 <= i < Zlength seg /\ ids i) _)).

Definition ProductReachable (seg : list Z) (p : Z) : Prop :=
  exists ids : Z -> Prop, SelectedProduct seg ids = p.

Definition ReachableDivisorProducts
    (x : Z) (seg products : list Z) : Prop :=
  NoDup products /\
  forall p,
    In p products <->
      1 <= p <= x /\ (exists k, x = p * k) /\ ProductReachable seg p.

(** The pure relation between the active product list and the byte table.
    Array length and ownership remain explicit C facts/resources. *)
Definition ValuableBitmap
    (x : Z) (products bitmap : list Z) : Prop :=
  forall p, 0 <= p <= x ->
    Znth p bitmap 0 =
      if in_dec Z.eq_dec p products then 1 else 0.

Definition ValuablePrefixCuts
    (x : Z) (a : list Z) (i segments : Z) (starts : list Z) : Prop :=
  Zlength starts = segments /\
  1 <= segments /\
  Znth 0 starts 0 = 0 /\
  mono_inc starts /\
  0 <= Znth (Zlength starts - 1) starts 0 <= i /\
  ((i = 0 /\ starts = (0 :: nil)) \/
   (0 < i /\ Znth (Zlength starts - 1) starts 0 < i)) /\
  (forall k, 0 <= k < Zlength starts - 1 ->
    BadCardSegment x
      (sublist (Znth k starts 0) (Znth (k + 1) starts 0) a)) /\
  BadCardSegment x
    (sublist (Znth (Zlength starts - 1) starts 0) i a) /\
  (forall alternative,
    BadPartition x (sublist 0 i a) alternative ->
    segments <= Zlength alternative - 1).

(** Outer-loop business state: the completed greedy cuts are already a lower
    bound for every partition of the processed prefix, and [products] exactly
    represents the reachable divisor products of the live final segment. *)
Definition ValuableOuterState
    (x : Z) (a : list Z) (i segments : Z) (products : list Z) : Prop :=
  exists starts,
    ValuablePrefixCuts x a i segments starts /\
    ReachableDivisorProducts x
      (sublist (Znth (Zlength starts - 1) starts 0) i a) products.

(** Inner-loop state after scanning [scanned] entries of the snapshot
    [base].  The list [products] is the old set plus precisely the valid
    products obtained by using the new card once, and [reaches] records whether
    x has appeared among those products. *)
Definition ValuableClosureState
    (x : Z) (seg : list Z) (v : Z) (base : list Z)
    (scanned : Z) (products : list Z) (reaches : Z) : Prop :=
  ReachableDivisorProducts x seg base /\
  NoDup products /\
  (forall p,
    In p products <->
      In p base \/
      exists q,
        In q (sublist 0 scanned base) /\
        p = q * v /\ 1 <= p <= x /\ exists k, x = p * k) /\
  ((reaches = 1 /\
      exists q, In q (sublist 0 scanned base) /\ q * v = x) \/
   (reaches = 0 /\
      forall q, In q (sublist 0 scanned base) -> q * v <> x)).

(** During reset, entries before [cleared] have been removed, so the bitmap
    represents exactly the as-yet uncleared suffix of the distinct product
    list. *)
Definition ValuableClearingState
    (x : Z) (products : list Z) (cleared : Z) (bitmap : list Z) : Prop :=
  ValuableBitmap x
    (sublist cleared (Zlength products) products) bitmap.

(** A strengthened greedy-history state carried in parallel with
    [ValuableOuterState].  The same cut-start witness is tied to the live
    reachable-product table, and every completed cut records the trigger that
    forced it: extending the preceding bad segment through the boundary card
    makes that segment non-bad. *)
Definition ValuableForcedHistory
    (x : Z) (a : list Z) (i segments : Z) (products : list Z) : Prop :=
  exists starts,
    ValuablePrefixCuts x a i segments starts /\
    ReachableDivisorProducts x
      (sublist (Znth (Zlength starts - 1) starts 0) i a) products /\
    forall k, 0 <= k < Zlength starts - 1 ->
      ~ BadCardSegment x
          (sublist (Znth k starts 0)
            (Znth (k + 1) starts 0 + 1) a).

(** Cumulative cut alignment for every competing partition of the current or
    a future input prefix.  The [k]-th alternative boundary is no later than
    the [k]-th completed greedy boundary.  Because both boundary lists are
    strictly increasing, these canonical boundaries are already an ordered
    injection; the explicit length conjunct is its counting consequence. *)
Definition ValuablePartitionAlignment
    (x : Z) (a : list Z) (processed segments : Z)
    (starts : list Z) : Prop :=
  forall endpoint alternative,
    processed <= endpoint <= Zlength a ->
    BadPartition x (sublist 0 endpoint a) alternative ->
    segments <= Zlength alternative - 1 /\
    forall k, 0 <= k < segments ->
      Znth k alternative 0 <= Znth k starts 0.

(** The revision-3 outer history keeps the old mathematical interfaces as
    projections, but additionally owns the cross-partition alignment needed
    to transport and increment the universal partition-count lower bound. *)
Definition ValuableAlignedHistory
    (x : Z) (a : list Z) (processed segments : Z)
    (products : list Z) : Prop :=
  exists starts,
    ValuablePrefixCuts x a processed segments starts /\
    ReachableDivisorProducts x
      (sublist (Znth (Zlength starts - 1) starts 0) processed a) products /\
    (forall k, 0 <= k < Zlength starts - 1 ->
      ~ BadCardSegment x
          (sublist (Znth k starts 0)
            (Znth (k + 1) starts 0 + 1) a)) /\
    ValuablePartitionAlignment x a processed segments starts.

Require Import Coq.micromega.Lia.

Require Import Coq.ZArith.Zquot.

Require Import Coq.micromega.Psatz.

Require Import Coq.Sorting.Permutation.

Require Import Coq.Logic.Classical_Prop.
