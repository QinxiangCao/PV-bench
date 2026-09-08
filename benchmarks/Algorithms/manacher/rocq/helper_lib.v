Require Import PVbench.Algorithms.manacher.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ManacherTransformedPrefix
    (s s2 : list Z) (i : Z) : Prop :=
  0 <= i <= Zlength s /\
  Zlength s2 = 2 * i + 1 /\
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
  (forall k,
      0 < k < len ->
        Znth k s2 0 <> 36) /\
  (forall k,
      0 <= k < Zlength s ->
        Znth (2 * k + 1) s2 0 = 35 /\
        Znth (2 * k + 2) s2 0 = Znth k s 0) /\
  (forall k,
      0 <= k < len ->
        Znth k s2 0 <> 0).

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
  CenterRadiusPalindrome s2 len center radius /\
  (center - radius < 0 \/
   len <= center + radius \/
   Znth (center - radius) s2 0 <> Znth (center + radius) s2 0).

(* The first [upto] entries of the radius table [p] have been computed and
   each stored radius is maximal for its center. *)
Definition RadiusTablePrefix
    (s2 : list Z) (len : Z) (p : list Z) (upto : Z) : Prop :=
  Zlength p = upto /\
  1 <= upto <= len /\
  forall k,
    1 <= k < upto ->
      CenterRadiusMaximal s2 len k (Znth k p 0).

(* The usual Manacher rightmost known palindrome window, represented by
   center [id] and right boundary [limit]. *)
Definition CurrentRightmostWindow
    (s2 : list Z) (len id limit : Z) : Prop :=
  0 <= id < len /\
  0 <= limit <= len /\
  (id < limit ->
    CenterRadiusPalindrome s2 len id (limit - id)).

(* The best palindrome found before [upto]: [maxId] is its center and
   [maxLen] is the original-string length, i.e. transformed radius minus one. *)
Definition BestRadiusPrefix
    (s2 : list Z) (len : Z) (p : list Z)
    (upto maxId maxLen : Z) : Prop :=
  1 <= upto <= len /\
  0 <= maxLen /\
  0 <= maxId < len /\
  ((maxLen = 0 /\ upto <= 2) \/
   CenterRadiusPalindrome s2 len maxId (maxLen + 1)) /\
  (forall k,
      1 <= k < upto -> Znth k p 0 - 1 <= maxLen) /\
  ((maxLen = 0 /\ upto <= 2) \/
   exists k,
     1 <= k < upto /\
     k = maxId /\
     Znth k p 0 - 1 = maxLen).

(* Main loop invariant after processing centers below [i].  It packages the
   transformed string, computed radius prefix, rightmost window, and best-so-far
   result used by later witnesses. *)
Definition ManacherLoopState
    (s s2 : list Z) (len : Z) (p : list Z)
    (i id limit maxId maxLen : Z) : Prop :=
  ManacherTransformedString s s2 len /\
  RadiusTablePrefix s2 len p i /\
  0 <= id < i /\
  CurrentRightmostWindow s2 len id limit /\
  BestRadiusPrefix s2 len p i maxId maxLen.

(* State at the start of an expansion attempt: current radius is already
   palindromic and the next compared pair is within or on the boundary. *)
Definition ExpansionCandidate
    (s2 : list Z) (len center radius : Z) : Prop :=
  1 <= center < len /\
  1 <= radius /\
  0 <= center - radius /\
  center + radius <= len /\
  CenterRadiusPalindrome s2 len center radius /\
  (Znth (center - radius) s2 0 = Znth (center + radius) s2 0 ->
   center + radius < len /\ 0 < center - radius).

(* The next compared pair matched, so expansion may safely increase radius. *)
Definition ExpansionAfterMatch
    (s2 : list Z) (len center radius : Z) : Prop :=
  ExpansionCandidate s2 len center radius /\
  center + radius < len /\
  0 < center - radius /\
  Znth (center - radius) s2 0 = Znth (center + radius) s2 0.

(* Invariant for the inner expansion loop for center [i], with [p_written]
   already containing the candidate radius at index [i]. *)
Definition ExpansionLoopState
    (s s2 : list Z) (len : Z) (p_written : list Z)
    (i r id limit maxId maxLen : Z) : Prop :=
  Zlength p_written = i + 1 /\
  ManacherLoopState s s2 len (sublist 0 i p_written)
                    i id limit maxId maxLen /\
  Znth i p_written 0 = r /\
  ExpansionCandidate s2 len i r.

(* Extract original-string characters from a transformed-string slice. *)
Definition NonHashChars (xs : list Z) : list Z :=
  filter (fun z => negb (Z.eqb z 35)) xs.

(* Progress invariant for copying the selected transformed window into output:
   [out] is exactly the non-# characters already visited. *)
Definition OutputCopyPrefix
    (s2 out : list Z) (start cur : Z) (j : Z) : Prop :=
  0 <= start /\
  start <= cur /\
  cur <= Zlength s2 /\
  out = NonHashChars (sublist start cur s2) /\
  j = Zlength out.

(* A lightweight bound used during output copying: any partial copied prefix
   has length at most [maxLen]. *)
Definition OutputCopyBound
    (s2 : list Z) (start cur maxLen : Z) : Prop :=
  0 <= start /\
  start <= cur /\
  cur <= Zlength s2 /\
  Zlength (NonHashChars (sublist start cur s2)) <= maxLen.

(* Final state after copying: the copied output corresponds to the selected
   best palindrome and satisfies the overall longest-palindrome spec. *)
Definition OutputCopyDone
    (s s2 out : list Z) (len maxId maxLen ret : Z) : Prop :=
  ManacherTransformedString s s2 len /\
  ret = maxLen /\
  OutputCopyPrefix s2 out (maxId - maxLen) (maxId + maxLen + 1) ret /\
  LongestPalindromeResult s out ret.
