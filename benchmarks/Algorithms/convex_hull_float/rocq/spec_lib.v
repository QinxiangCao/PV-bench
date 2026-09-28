Require Import SumLib.ZRange.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From compcert.lib Require Import Integers.
From Flocq.IEEE754 Require Import Bits.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib FloatLib.

Require Export PVbench.Algorithms.convex_hull_float.rocq.pointf_model.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.
Local Close Scope string_scope.

Definition pointf_permutation : list PointF -> list PointF -> Prop :=
  @Permutation PointF.

Definition pointf_xy_sorted_range
    (l : list PointF) (lo hi : Z) : Prop :=
  forall i j, lo <= i <= j -> j <= hi ->
    pointf_cmp_xy (Znth i l default_pointf)
                  (Znth j l default_pointf) <= 0.

Definition pointf_xy_sorted (l : list PointF) : Prop :=
  pointf_xy_sorted_range l 0 (Zlength l - 1).

Definition pointf_ccw (a b c : PointF) : Prop :=
  fp32_gt (pointf_cross a b c) fp32_zero.

Definition pointf_drop_last (l : list PointF) : list PointF := removelast l.

Definition pointf_pop_step (p : PointF) (before after : list PointF) : Prop :=
  2 <= Zlength before /\
  ~ pointf_ccw (Znth (Zlength before - 2) before default_pointf)
               (Znth (Zlength before - 1) before default_pointf) p /\
  after = removelast before.
Definition pointf_pop_trace (p : PointF) : list PointF -> list PointF -> Prop :=
  Relation_Operators.clos_refl_trans _ (pointf_pop_step p).
Definition pointf_pop_stopped (p : PointF) (chain : list PointF) : Prop :=
  Zlength chain < 2 \/
  (2 <= Zlength chain /\
   pointf_ccw (Znth (Zlength chain - 2) chain default_pointf)
              (Znth (Zlength chain - 1) chain default_pointf) p).
Definition pointf_pop_until (p : PointF) (before after : list PointF) : Prop :=
  pointf_pop_trace p before after /\ pointf_pop_stopped p after.

Definition pointf_upper_pop_step (lower_bound : Z) (p : PointF)
    (before after : list PointF) : Prop :=
  lower_bound < Zlength before /\ pointf_pop_step p before after.
Definition pointf_upper_pop_trace (lower_bound : Z) (p : PointF)
    : list PointF -> list PointF -> Prop :=
  Relation_Operators.clos_refl_trans _ (pointf_upper_pop_step lower_bound p).
Definition pointf_upper_pop_stopped (lower_bound : Z) (p : PointF)
    (chain : list PointF) : Prop :=
  Zlength chain <= lower_bound \/ Zlength chain < 2 \/
  (lower_bound < Zlength chain /\ 2 <= Zlength chain /\
   pointf_ccw (Znth (Zlength chain - 2) chain default_pointf)
              (Znth (Zlength chain - 1) chain default_pointf) p).
Definition pointf_upper_pop_until (lower_bound : Z) (p : PointF)
    (before after : list PointF) : Prop :=
  pointf_upper_pop_trace lower_bound p before after /\
  pointf_upper_pop_stopped lower_bound p after.

Definition pointf_scan_step (before : list PointF) (p : PointF)
    (after : list PointF) : Prop :=
  exists reduced, pointf_pop_until p before reduced /\ after = reduced ++ [p].
Definition pointf_upper_scan_step (bound : Z)
    (before : list PointF) (p : PointF) (after : list PointF) : Prop :=
  exists reduced, pointf_upper_pop_until bound p before reduced /\
    after = reduced ++ [p].
Definition pointf_scan_transition
    (step : list PointF -> PointF -> list PointF -> Prop)
    (before after : list PointF * list PointF) : Prop :=
  exists p, fst after = fst before ++ [p] /\ step (snd before) p (snd after).
Definition pointf_scan_from (initial input after : list PointF) : Prop :=
  Relation_Operators.clos_refl_trans _ (pointf_scan_transition pointf_scan_step)
    ([], initial) (input, after).
Definition pointf_upper_scan_from (bound : Z)
    (initial input after : list PointF) : Prop :=
  Relation_Operators.clos_refl_trans _
    (pointf_scan_transition (pointf_upper_scan_step bound))
    ([], initial) (input, after).
Definition is_andrew_hull_float (input sorted hull : list PointF) : Prop :=
  pointf_permutation input sorted /\ pointf_xy_sorted sorted /\
  if Z.leb (Zlength sorted) 1 then hull = sorted else
    exists lower combined,
      pointf_scan_from [] sorted lower /\
      pointf_upper_scan_from (Zlength lower) lower
        (rev (sublist 0 (Zlength sorted - 1) sorted)) combined /\
      hull = pointf_drop_last combined.
