Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition AlnumCode (z : Z) : Prop :=
  (48 <= z <= 57) \/ (65 <= z <= 90) \/ (97 <= z <= 122).

(* Pointwise alphanumeric condition for the logical model of the C string. *)
Definition AlnumString (s : list Z) : Prop :=
  forall k, 0 <= k < Zlength s -> AlnumCode (Znth k s 0).

(* A substring [s[lo, lo+len)) is a palindrome in the original string. *)
Definition PalindromeSegment (s : list Z) (lo len : Z) : Prop :=
  0 <= lo /\
  0 <= len /\
  lo + len <= Zlength s /\
  forall k, 0 <= k < len ->
    Znth (lo + k) s 0 = Znth (lo + len - 1 - k) s 0.

(* Final functional postcondition: [out] is a longest palindromic substring
   of [s], and [ret] is exactly its length. *)
Definition LongestPalindromeResult
    (s out : list Z) (ret : Z) : Prop :=
  ret = Zlength out /\
  exists lo,
    out = sublist lo (lo + ret) s /\
    PalindromeSegment s lo ret /\
    forall lo' len',
      PalindromeSegment s lo' len' -> len' <= ret.

(* Prefix shape while building the transformed string:
   "$#s0#s1#..." up to the first [i] input characters. *)
