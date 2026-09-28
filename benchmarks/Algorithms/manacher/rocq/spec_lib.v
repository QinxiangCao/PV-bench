Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents VMap.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

(* Input characters are restricted to alphanumeric ASCII codes, so they
   cannot collide with Manacher's marker characters '$', '#', and '\0'. *)
Definition AlnumCode (z : Z) : Prop :=
  (48 <= z <= 57) \/ (65 <= z <= 90) \/ (97 <= z <= 122).

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
    max_value_of_subset Z.le
      (fun candidate : Z * Z =>
        PalindromeSegment s (fst candidate) (snd candidate))
      (@snd Z Z) ret.
