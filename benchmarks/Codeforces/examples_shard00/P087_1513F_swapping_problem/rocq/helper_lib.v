Require Export PVbench.Codeforces.examples_shard00.P087_1513F_swapping_problem.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Strings.String.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import Coq.micromega.Lia.

From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.

Local Open Scope Z_scope.

Import ListNotations.

Import naive_C_Rules.

Local Open Scope sac.

Local Open Scope string_scope.

Definition SegmentAllocationSize (size capacity : Z) : Prop :=
  size = capacity * sizeof_front_end_type (FET_alias "<anonymous struct>").

Definition SegmentProper (s : Z * Z) : Prop := fst s < snd s.

Definition SegmentsProper (segments : list (Z * Z)) : Prop :=
  Forall SegmentProper segments.

Definition SegmentsBounded (segments : list (Z * Z)) : Prop :=
  Forall (fun s => 1 <= fst s /\ fst s < snd s /\ snd s <= 1000000000)
         segments.

Definition SegmentsSortedByLeft (segments : list (Z * Z)) : Prop :=
  forall i j,
    0 <= i /\ i <= j /\ j < Zlength segments ->
    fst (Znth i segments (0, 0)) <= fst (Znth j segments (0, 0)).

Definition IncreasingIntervals
    (a b : list Z) (limit : Z) : list (Z * Z) :=
  map (fun i => (Znth i a 0, Znth i b 0))
      (filter (fun i => (Znth i a 0 <? Znth i b 0)%Z)
              (Zrange 0 limit)).

Definition DecreasingIntervals
    (a b : list Z) (limit : Z) : list (Z * Z) :=
  map (fun i => (Znth i b 0, Znth i a 0))
      (filter (fun i => (Znth i b 0 <? Znth i a 0)%Z)
              (Zrange 0 limit)).

Definition PairDistancePrefix (a b : list Z) (limit : Z) : Z :=
  fold_right Z.add 0
    (Zmap_range
       (fun i => Z.abs (Znth i a 0 - Znth i b 0)) limit).

(** Stable mathematical state of the classification pass in [solver]. *)
Definition SolverScanState
    (a b : list Z) (limit base : Z)
    (increasing decreasing : list (Z * Z)) : Prop :=
  increasing = IncreasingIntervals a b limit /\
  decreasing = DecreasingIntervals a b limit /\
  base = PairDistancePrefix a b limit.

Definition IntervalOverlap (s t : Z * Z) : Z :=
  Z.max 0 (Z.min (snd s) (snd t) - Z.max (fst s) (fst t)).

(** Candidates considered by one directed call of [overlap]. *)
Definition DirectedOverlapCandidatePrefix
    (left right : list (Z * Z)) (limit value : Z) : Prop :=
  value = 0 \/
  exists i j,
    0 <= i < limit /\ 0 <= j < Zlength right /\
    fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) /\
    value = IntervalOverlap (Znth i left (0, 0))
                            (Znth j right (0, 0)).

Definition DirectedOverlapMaximumPrefix
    (left right : list (Z * Z)) (limit best : Z) : Prop :=
  max_value_of_subset Z.le
    (DirectedOverlapCandidatePrefix left right limit)
    (fun value => value) best.

Definition DirectedOverlapMaximum
    (left right : list (Z * Z)) (best : Z) : Prop :=
  DirectedOverlapMaximumPrefix left right (Zlength left) best.

(** Prefix maxima of right endpoints in a list sorted by left endpoint. *)
Definition PrefixRightMaxima
    (segments : list (Z * Z)) (prefix : list Z) (limit : Z) : Prop :=
  Zlength prefix = limit /\
  forall i,
    0 <= i < limit ->
    max_value_of_subset Z.le
      (fun j : Z => 0 <= j <= i)
      (fun j => snd (Znth j segments (0, 0)))
      (Znth i prefix 0).

(** Binary-search bracket for the first segment whose left endpoint exceeds
    [key].  Bounds remain in the C invariant; this predicate owns only the
    mathematical partition of the sorted search space. *)
Definition UpperBoundBracket
    (segments : list (Z * Z)) (key lo hi : Z) : Prop :=
  (forall j, 0 <= j < lo ->
     fst (Znth j segments (0, 0)) <= key) /\
  (forall j, hi <= j < Zlength segments ->
     key < fst (Znth j segments (0, 0))).

(** The final, symmetric overlap optimized by the two directed calls. *)
Definition SwappingOverlapCandidate
    (a b : list Z) (value : Z) : Prop :=
  value = 0 \/
  exists s t,
    In s (IncreasingIntervals a b (Zlength a)) /\
    In t (DecreasingIntervals a b (Zlength a)) /\
    value = IntervalOverlap s t.

Definition SwappingOverlapMaximum
    (a b : list Z) (best : Z) : Prop :=
  max_value_of_subset Z.le
    (SwappingOverlapCandidate a b) (fun value => value) best.

Require Import Coq.Sorting.Permutation.
