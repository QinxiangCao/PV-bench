Require Import PVbench.Algorithms.convex_hull_float.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From compcert.lib Require Import Integers.
From Flocq.IEEE754 Require Import Bits.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib FloatLib.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Local Close Scope string_scope.

Definition pointf_same_outside_range
    (before cur : list PointF) (lo hi : Z) : Prop :=
  Zlength before = Zlength cur /\
  forall k,
    0 <= k < Zlength before ->
    (k < lo \/ hi < k) ->
    Znth k cur default_pointf = Znth k before default_pointf.
Definition pointf_xy_partitioned_at
    (l : list PointF) (lo hi pivot : Z) : Prop :=
  lo <= pivot <= hi /\
  Forall
    (fun p => pointf_cmp_xy p (Znth pivot l default_pointf) <= 0)
    (sublist lo pivot l) /\
  Forall
    (fun p => pointf_cmp_xy (Znth pivot l default_pointf) p < 0)
    (sublist (pivot + 1) (hi + 1) l).
Definition pointf_xy_partition_scan_inv
    (before cur : list PointF)
    (lo hi : Z) (pivot : PointF) (split scan : Z) : Prop :=
  pointf_permutation before cur /\
  pointf_same_outside_range before cur lo hi /\
  Znth hi cur default_pointf = pivot /\
  (forall k,
     lo <= k <= split ->
     pointf_cmp_xy (Znth k cur default_pointf) pivot <= 0) /\
  (forall k,
     split < k < scan ->
     pointf_cmp_xy pivot (Znth k cur default_pointf) < 0).
Inductive pointf_pop_trace (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_pop_trace_refl : forall s,
    pointf_pop_trace p s s
| pointf_pop_trace_pop : forall before cur,
    pointf_pop_trace p before cur ->
    2 <= Zlength cur ->
    ~ pointf_ccw (Znth (Zlength cur - 2) cur default_pointf)
                 (Znth (Zlength cur - 1) cur default_pointf) p ->
    pointf_pop_trace p before (removelast cur).
Inductive pointf_upper_pop_trace
    (lower_bound : Z) (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_upper_pop_trace_refl : forall s,
    pointf_upper_pop_trace lower_bound p s s
| pointf_upper_pop_trace_pop : forall before cur,
    pointf_upper_pop_trace lower_bound p before cur ->
    lower_bound < Zlength cur ->
    2 <= Zlength cur ->
    ~ pointf_ccw (Znth (Zlength cur - 2) cur default_pointf)
                 (Znth (Zlength cur - 1) cur default_pointf) p ->
    pointf_upper_pop_trace lower_bound p before (removelast cur).
Definition pointf_lower_scan_inv
    (sorted chain : list PointF) (read top : Z) : Prop :=
  0 <= read <= Zlength sorted /\ top = Zlength chain /\
  pointf_scan_from [] (sublist 0 read sorted) chain /\
  (Zlength sorted <= read -> 2 <= top).
Definition pointf_lower_pop_inv
    (sorted before chain : list PointF) (read top : Z) : Prop :=
  pointf_lower_scan_inv sorted before read (Zlength before) /\
  pointf_pop_trace (Znth read sorted default_pointf) before chain /\
  top = Zlength chain.
Definition pointf_upper_capacity
    (sorted chain : list PointF) (read lower_n : Z) : Prop :=
  lower_n <= Zlength sorted /\
  Zlength chain <= lower_n + (Zlength sorted - read) /\
  (1 <= read -> Zlength chain < 2 * Zlength sorted) /\
  (read <= 0 -> lower_n < Zlength chain).
Definition pointf_upper_scan_inv
    (sorted lower chain : list PointF) (read top lower_n : Z) : Prop :=
  0 <= read <= Zlength sorted /\ top = Zlength chain /\
  lower_n = Zlength lower /\
  lower = sublist 0 lower_n chain /\
  lower_n <= top /\
  pointf_scan_from [] sorted lower /\
  pointf_upper_scan_from lower_n lower
    (rev (sublist read (Zlength sorted - 1) sorted)) chain /\
  pointf_upper_capacity sorted chain read lower_n.
Definition pointf_upper_pop_inv
    (sorted lower before chain : list PointF) (read top lower_n : Z) : Prop :=
  pointf_upper_scan_inv sorted lower before (read + 1) (Zlength before) lower_n /\
  pointf_upper_pop_trace lower_n (Znth read sorted default_pointf) before chain /\
  top = Zlength chain /\
  lower = sublist 0 lower_n chain /\
  lower_n <= top.
