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

(* Bit-level companions used by the float field projection strategies. *)
Definition store_pointf_x_bits (p : addr) (bits : Z) : Assertion :=
  poly_store FET_float p bits.
Definition store_pointf_y_bits (p : addr) (bits : Z) : Assertion :=
  poly_store FET_float p bits.

Local Close Scope string_scope.

Definition pointf_swap (l : list PointF) (i j : Z) : list PointF :=
  replace_Znth j (Znth i l default_pointf)
    (replace_Znth i (Znth j l default_pointf) l).

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
