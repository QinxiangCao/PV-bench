Require Export PVbench.Algorithms.manacher.rocq.spec_lib.
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

(* Prefix shape while building the transformed string:
   "$#s0#s1#..." up to the first [i] input characters. *)
Definition ManacherTransformedPrefix
    (s s2 : list Z) (i : Z) : Prop :=
  Znth 0 s2 0 = 36 /\
  forall k,
    0 <= k < i ->
      Znth (2 * k + 1) s2 0 = 35 /\
      Znth (2 * k + 2) s2 0 = Znth k s 0.

(* Complete transformed string used by the C implementation:
   '$' at index 0, alternating '#' and input characters, final '#',
   and a trailing '\0' outside the logical Manacher length [len]. *)
Definition ManacherTransformedString
    (s s2 : list Z) (len : Z) : Prop :=
  len = 2 * Zlength s + 2 /\
  Zlength s2 = len + 1 /\
  Znth 0 s2 0 = 36 /\
  Znth (len - 1) s2 0 = 35 /\
  Znth len s2 0 = 0 /\
  Forall (fun ch => ch <> 36) (sublist 1 len s2) /\
  (forall k,
      0 <= k < Zlength s ->
        Znth (2 * k + 1) s2 0 = 35 /\
        Znth (2 * k + 2) s2 0 = Znth k s 0) /\
  Forall (fun ch => ch <> 0) (sublist 0 len s2).

(* In the transformed string, [radius] means all offsets [0, radius) around
   [center] are symmetric and stay inside [0, len). *)
Definition CenterRadiusPalindrome
    (s2 : list Z) (len center radius : Z) : Prop :=
  1 <= center < len /\
  1 <= radius /\
  0 <= center - (radius - 1) /\
  center + (radius - 1) < len /\
  forall d,
    0 <= d < radius ->
      Znth (center - d) s2 0 = Znth (center + d) s2 0.

(* A center radius is maximal if it is palindromic and cannot be extended
   because it hits a boundary or a mismatching pair. *)
Definition CenterRadiusMaximal
    (s2 : list Z) (len center radius : Z) : Prop :=
  max_value_of_subset Z.le (CenterRadiusPalindrome s2 len center)
    (fun r : Z => r) radius.

(* The first [upto] entries of the radius table [p] have been computed and
   each stored radius is maximal for its center. *)
Definition RadiusTablePrefix
    (s2 : list Z) (len : Z) (p : list Z) (upto : Z) : Prop :=
  forall k,
    1 <= k < upto ->
      CenterRadiusMaximal s2 len k (Znth k p 0).

(* The usual Manacher rightmost known palindrome window, represented by
   center [id] and right boundary [limit]. *)
Definition CurrentRightmostWindow
    (s2 : list Z) (len id limit : Z) : Prop :=
  (id < limit ->
    CenterRadiusPalindrome s2 len id (limit - id)).

(* The best palindrome found before [upto]: [maxId] is its center and
   [maxLen] is the original-string length, i.e. transformed radius minus one. *)
Definition BestRadiusPrefix
    (s2 : list Z) (len : Z) (p : list Z)
    (upto maxId maxLen : Z) : Prop :=
  (maxLen = 0 \/
   CenterRadiusPalindrome s2 len maxId (maxLen + 1)) /\
  max_value_of_subset Z.le
    (fun v => v = 0 \/ exists k,
      1 <= k < upto /\ v = Znth k p 0 - 1)
    (fun v : Z => v) maxLen /\
  (maxLen = 0 \/
   exists k, 1 <= k < upto /\ k = maxId /\ Znth k p 0 - 1 = maxLen).

(* Main loop invariant after processing centers below [i].  It packages the
   transformed string, computed radius prefix, rightmost window, and best-so-far
   result used by later witnesses. *)
Definition ManacherLoopState
    (s s2 : list Z) (len : Z) (p : list Z)
    (i id limit maxId maxLen : Z) : Prop :=
  ManacherTransformedString s s2 len /\
  RadiusTablePrefix s2 len p i /\
  CurrentRightmostWindow s2 len id limit /\
  BestRadiusPrefix s2 len p i maxId maxLen.

(* The radius stored at the current center is palindromic.  The next-read
   bounds are stated separately in the C invariant. *)
Definition ExpansionLoopState
    (s s2 : list Z) (len : Z) (p_written : list Z)
    (i r id limit maxId maxLen : Z) : Prop :=
  ManacherLoopState s s2 len (sublist 0 i p_written)
                    i id limit maxId maxLen /\
  Znth i p_written 0 = r /\
  CenterRadiusPalindrome s2 len i r.

(* Extract original-string characters from a transformed-string slice. *)
Definition NonHashChars (xs : list Z) : list Z :=
  filter (fun z => negb (Z.eqb z 35)) xs.

(* Progress invariant for copying the selected transformed window into output:
   [out] is exactly the non-# characters already visited. *)
Definition OutputCopyPrefix
    (s2 out : list Z) (start cur : Z) (j : Z) : Prop :=
  out = NonHashChars (sublist start cur s2) /\
  j = Zlength out.
