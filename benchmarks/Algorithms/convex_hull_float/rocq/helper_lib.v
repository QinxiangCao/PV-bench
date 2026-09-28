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

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.


Require Export PVbench.Algorithms.convex_hull_float.rocq.spec_lib.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.
Local Close Scope string_scope.

Definition pointf_same_outside_range
    (before cur : list PointF) (lo hi : Z) : Prop :=
  Zlength before = Zlength cur /\
  Forall2 eq
    (map (fun k => Znth k cur default_pointf)
      (filter (fun k : Z => orb (Z.ltb k lo) (Z.ltb hi k)) (Zrange 0 (Zlength before))))
    (map (fun k => Znth k before default_pointf)
      (filter (fun k : Z => orb (Z.ltb k lo) (Z.ltb hi k)) (Zrange 0 (Zlength before)))).
Definition pointf_xy_partitioned_at
    (l : list PointF) (lo hi pivot : Z) : Prop :=
  lo <= pivot <= hi /\
  Forall
    (fun p => pointf_cmp_xy p (Znth pivot l default_pointf) <= 0)
    (sublist lo pivot l) /\
  Forall
    (fun p => pointf_cmp_xy (Znth pivot l default_pointf) p < 0)
    (sublist (pivot + 1) (hi + 1) l).

Definition pointf_lower_scan_inv (sorted chain : list PointF) (read top : Z) : Prop :=
  pointf_scan_from [] (sublist 0 read sorted) chain.
Definition pointf_lower_pop_inv (sorted before chain : list PointF) (read top : Z) : Prop :=
  pointf_lower_scan_inv sorted before read (Zlength before) /\
  pointf_pop_trace (Znth read sorted default_pointf) before chain.
Definition pointf_upper_scan_inv
    (sorted lower chain : list PointF) (read top lower_n : Z) : Prop :=
  lower = sublist 0 lower_n chain /\
  pointf_scan_from [] sorted lower /\
  pointf_upper_scan_from lower_n lower
    (rev (sublist read (Zlength sorted - 1) sorted)) chain.
Definition pointf_upper_pop_inv
    (sorted lower before chain : list PointF) (read top lower_n : Z) : Prop :=
  pointf_upper_scan_inv sorted lower before (read + 1) (Zlength before) lower_n /\
  pointf_upper_pop_trace lower_n (Znth read sorted default_pointf) before chain /\
  lower = sublist 0 lower_n chain.
Definition pointf_xy_partition_scan_inv
    (before cur : list PointF) (lo hi : Z) (pivot : PointF) (split scan : Z) : Prop :=
  pointf_permutation before cur /\ pointf_same_outside_range before cur lo hi /\
  Znth hi cur default_pointf = pivot /\
  Forall (fun p => pointf_cmp_xy p pivot <= 0) (sublist lo (split + 1) cur) /\
  Forall (fun p => pointf_cmp_xy pivot p < 0) (sublist (split + 1) scan cur).
