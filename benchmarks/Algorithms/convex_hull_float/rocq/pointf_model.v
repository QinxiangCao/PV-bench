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

Definition pointf_get_x (p : PointF) : fp32 := pointf_x p.
Definition pointf_get_y (p : PointF) : fp32 := pointf_y p.

Definition default_pointf : PointF :=
  pointf_mk fp32_zero fp32_zero.

Axiom sizeof_PointF :
  sizeof_front_end_type (FET_alias "PointF") = 8.

Definition store_pointf (p : addr) (pt : PointF) : Assertion :=
  (&((p) # "PointF" ->ₛ "x") # Float |-> pointf_x pt) **
  (&((p) # "PointF" ->ₛ "y") # Float |-> pointf_y pt).

Definition undef_pointf (p : addr) : Assertion :=
  (&((p) # "PointF" ->ₛ "x") # Float |->_) **
  (&((p) # "PointF" ->ₛ "y") # Float |->_).

Module StorePointFAsElement <: ELEMENT_STORE.
  Definition A := PointF.
  Definition sizeA : Z := sizeof_front_end_type (FET_alias "PointF").
  Definition storeA (base : addr) (lo : Z) (a : PointF) : Assertion :=
    store_pointf (base + lo * sizeA) a.
  Definition undefstoreA (base : addr) (lo : Z) : Assertion :=
    undef_pointf (base + lo * sizeA).

  Lemma store_to_undefstore : forall base lo a,
    storeA base lo a |-- undefstoreA base lo.
  Proof.
    intros. unfold storeA, undefstoreA, store_pointf, undef_pointf.
    sep_apply store_float_undef_store_float.
    sep_apply store_float_undef_store_float.
    cancel.
  Qed.

  Lemma storeA_shift : forall base n lo a,
    storeA (base + n * sizeA) lo a --||-- storeA base (lo + n) a.
  Proof.
    intros. unfold storeA.
    replace (base + n * sizeA + lo * sizeA)
      with (base + (lo + n) * sizeA) by lia.
    split; reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall base n lo,
    undefstoreA (base + n * sizeA) lo --||-- undefstoreA base (lo + n).
  Proof.
    intros. unfold undefstoreA.
    replace (base + n * sizeA + lo * sizeA)
      with (base + (lo + n) * sizeA) by lia.
    split; reflexivity.
  Qed.

  Lemma store_to_align : forall base lo a,
    storeA base lo a |-- store_align_n sizeA.
  Proof.
    intros. unfold storeA, store_pointf, sizeA.
    rewrite sizeof_PointF.
    sep_apply store_float_align4.
    sep_apply store_float_align4.
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma undefstore_to_align : forall base lo,
    undefstoreA base lo |-- store_align_n sizeA.
  Proof.
    intros. unfold undefstoreA, undef_pointf, sizeA.
    rewrite sizeof_PointF.
    sep_apply undef_store_float_align4.
    sep_apply undef_store_float_align4.
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA. rewrite sizeof_PointF.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.
End StorePointFAsElement.

Local Close Scope string_scope.

Module PointFArray := ArrayLib (StorePointFAsElement).

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

(* Bit-level companions used by the float field projection strategies. *)
Definition store_pointf_x_bits (p : addr) (bits : Z) : Assertion :=
  poly_store FET_float p bits.

Definition store_pointf_y_bits (p : addr) (bits : Z) : Assertion :=
  poly_store FET_float p bits.

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

Definition pointf_swap (l : list PointF) (i j : Z) : list PointF :=
  replace_Znth j (Znth i l default_pointf)
    (replace_Znth i (Znth j l default_pointf) l).
