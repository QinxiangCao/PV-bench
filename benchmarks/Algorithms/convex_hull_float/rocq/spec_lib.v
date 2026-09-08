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

Record PointF : Type := pointf_mk {
  pointf_x : fp32;
  pointf_y : fp32
}.
Definition default_pointf : PointF :=
  pointf_mk fp32_zero fp32_zero.

Definition pointf_get_x (p : PointF) : fp32 := pointf_x p.
Definition pointf_get_y (p : PointF) : fp32 := pointf_y p.

Definition store_pointf (p : addr) (pt : PointF) : Assertion :=
  (&((p) # "PointF" ->ₛ "x") # Float |-> pointf_x pt) **
  (&((p) # "PointF" ->ₛ "y") # Float |-> pointf_y pt).

Definition undef_pointf (p : addr) : Assertion :=
  (&((p) # "PointF" ->ₛ "x") # Float |->_) **
  (&((p) # "PointF" ->ₛ "y") # Float |->_).

Module PointFArray.
  Definition A := PointF.
  Definition sizeA : Z := 8.
  Definition storeA (base : addr) (lo : Z) (a : A) : Assertion :=
    store_pointf (base + lo * sizeA) a.
  Definition undefstoreA (base : addr) (lo : Z) : Assertion :=
    undef_pointf (base + lo * sizeA).
  Definition seg (x lo hi : Z) (l : list A) : Assertion :=
    store_array_rec storeA x lo hi l.
  Definition missing_i (x i lo hi : Z) (l : list A) : Assertion :=
    store_array_missing_i_rec storeA x i lo hi l.
  Definition full (x n : Z) (l : list A) : Assertion :=
    store_array storeA x n l.
  Definition undef_seg (x lo hi : Z) : Assertion :=
    store_undef_array_rec undefstoreA x lo hi (Z.to_nat (hi - lo)).
  Definition undef_full (x n : Z) : Assertion :=
    store_undef_array undefstoreA x n.
End PointFArray.

Local Close Scope string_scope.

Definition pointf_finite (p : PointF) : Prop :=
  fp32_isFinite (pointf_x p) /\ fp32_isFinite (pointf_y p).
Definition pointsf_finite (l : list PointF) : Prop :=
  Forall pointf_finite l.
Definition pointf_cmp_xy (a b : PointF) : Z :=
  match fp32_compare (pointf_x a) (pointf_x b) with
  | Some Datatypes.Lt => -1
  | Some Datatypes.Gt => 1
  | Some Datatypes.Eq =>
      match fp32_compare (pointf_y a) (pointf_y b) with
      | Some Datatypes.Lt => -1
      | Some Datatypes.Gt => 1
      | _ => 0
      end
  | _ => 0
  end.
Definition pointf_cross (a b c : PointF) : fp32 :=
  fp32_sub
    (fp32_mul (fp32_sub (pointf_x b) (pointf_x a))
              (fp32_sub (pointf_y c) (pointf_y a)))
    (fp32_mul (fp32_sub (pointf_y b) (pointf_y a))
              (fp32_sub (pointf_x c) (pointf_x a))).
Definition pointf_cross_finite (a b c : PointF) : Prop :=
  fp32_isFinite (fp32_sub (pointf_x b) (pointf_x a)) /\
  fp32_isFinite (fp32_sub (pointf_y c) (pointf_y a)) /\
  fp32_isFinite (fp32_sub (pointf_y b) (pointf_y a)) /\
  fp32_isFinite (fp32_sub (pointf_x c) (pointf_x a)) /\
  fp32_isFinite
    (fp32_mul (fp32_sub (pointf_x b) (pointf_x a))
              (fp32_sub (pointf_y c) (pointf_y a))) /\
  fp32_isFinite
    (fp32_mul (fp32_sub (pointf_y b) (pointf_y a))
              (fp32_sub (pointf_x c) (pointf_x a))) /\
  fp32_isFinite (pointf_cross a b c).
Definition all_pointf_cross_finite (l : list PointF) : Prop :=
  forall a b c, In a l -> In b l -> In c l -> pointf_cross_finite a b c.
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
Inductive pointf_pop_until (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_pop_until_short : forall s,
    Zlength s < 2 -> pointf_pop_until p s s
| pointf_pop_until_ccw : forall s,
    2 <= Zlength s ->
    pointf_ccw (Znth (Zlength s - 2) s default_pointf)
               (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_pop_until p s s
| pointf_pop_until_pop : forall s out,
    2 <= Zlength s ->
    ~ pointf_ccw (Znth (Zlength s - 2) s default_pointf)
                 (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_pop_until p (removelast s) out ->
    pointf_pop_until p s out.
Inductive pointf_upper_pop_until
    (lower_bound : Z) (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_upper_pop_until_boundary : forall s,
    Zlength s <= lower_bound -> pointf_upper_pop_until lower_bound p s s
| pointf_upper_pop_until_short : forall s,
    Zlength s < 2 -> pointf_upper_pop_until lower_bound p s s
| pointf_upper_pop_until_ccw : forall s,
    lower_bound < Zlength s ->
    2 <= Zlength s ->
    pointf_ccw (Znth (Zlength s - 2) s default_pointf)
               (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_upper_pop_until lower_bound p s s
| pointf_upper_pop_until_pop : forall s out,
    lower_bound < Zlength s ->
    2 <= Zlength s ->
    ~ pointf_ccw (Znth (Zlength s - 2) s default_pointf)
                 (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_upper_pop_until lower_bound p (removelast s) out ->
    pointf_upper_pop_until lower_bound p s out.
Definition pointf_scan_step
    (before : list PointF) (p : PointF) (after : list PointF) : Prop :=
  exists reduced,
    pointf_pop_until p before reduced /\ after = reduced ++ [p].
Inductive pointf_scan_from : list PointF -> list PointF -> list PointF -> Prop :=
| pointf_scan_from_nil : forall initial,
    pointf_scan_from initial [] initial
| pointf_scan_from_snoc : forall initial input before p after,
    pointf_scan_from initial input before ->
    pointf_scan_step before p after ->
    pointf_scan_from initial (input ++ [p]) after.
Definition pointf_upper_scan_step
    (lower_bound : Z)
    (before : list PointF) (p : PointF) (after : list PointF) : Prop :=
  exists reduced,
    pointf_upper_pop_until lower_bound p before reduced /\
    after = reduced ++ [p].
Inductive pointf_upper_scan_from
    (lower_bound : Z) : list PointF -> list PointF -> list PointF -> Prop :=
| pointf_upper_scan_from_nil : forall initial,
    pointf_upper_scan_from lower_bound initial [] initial
| pointf_upper_scan_from_snoc : forall initial input before p after,
    pointf_upper_scan_from lower_bound initial input before ->
    pointf_upper_scan_step lower_bound before p after ->
    pointf_upper_scan_from lower_bound initial (input ++ [p]) after.
Definition pointf_drop_last (l : list PointF) : list PointF := removelast l.
Definition is_andrew_hull_float
    (input sorted hull : list PointF) : Prop :=
  pointf_permutation input sorted /\
  pointf_xy_sorted sorted /\
  if Z.leb (Zlength sorted) 1 then
    hull = sorted
  else
    exists lower combined,
      pointf_scan_from [] sorted lower /\
      pointf_upper_scan_from (Zlength lower) lower
        (rev (sublist 0 (Zlength sorted - 1) sorted)) combined /\
      hull = pointf_drop_last combined.
