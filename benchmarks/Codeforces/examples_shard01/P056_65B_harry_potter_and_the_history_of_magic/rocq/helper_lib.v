Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P056_65B_harry_potter_and_the_history_of_magic.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(** The ordinary decimal digits of a four-digit input year. *)
Definition YearDigits (y : Z) : list Z :=
  [y / 1000; y / 100 mod 10; y / 10 mod 10; y mod 10].

Definition DigitsValue (d : list Z) : Z :=
  1000 * Znth 0 d 0 + 100 * Znth 1 d 0 +
  10 * Znth 2 d 0 + Znth 3 d 0.

Definition DigitLower (pos : Z) : Z :=
  if Z.eq_dec pos 0 then 1 else 0.

(** The year obtained by choosing [v] for digit [pos].  This is a finite
    mathematical candidate description, not an execution model of the C
    loops. *)
Definition CandidateValue (y pos v : Z) : Z :=
  DigitsValue (replace_Znth pos v (YearDigits y)).

Definition LegalNext (y prev cand : Z) : Prop :=
  1000 <= cand <= 2011 /\ prev <= cand /\ AtMostOneDigit y cand.

Definition CursorCandidate (y pos next cand : Z) : Prop :=
  exists p v,
    0 <= p < 4 /\ DigitLower p <= v <= 9 /\
    (p < pos \/ (p = pos /\ v < next)) /\
    cand = CandidateValue y p v.

(** [best] is the minimum legal candidate in the finite part of the digit
    search selected by [(pos,next)], or [-1] when that part is empty. *)
Definition BestScanned (y prev pos next best : Z) : Prop :=
  (best = -1 /\
   forall cand, CursorCandidate y pos next cand -> ~ LegalNext y prev cand) \/
  (CursorCandidate y pos next best /\ LegalNext y prev best /\
   forall cand, CursorCandidate y pos next cand ->
                LegalNext y prev cand -> best <= cand).

Definition MinimalNext (y prev best : Z) : Prop :=
  LegalNext y prev best /\
  forall cand, LegalNext y prev cand -> best <= cand.

Definition NextYearResult (y prev result : Z) : Prop :=
  (result = -1 /\ forall cand, ~ LegalNext y prev cand) \/
  MinimalNext y prev result.

Definition PreviousYear (out : list Z) : Z :=
  if Z.eq_dec (Zlength out) 0 then 1000
  else Znth (Zlength out - 1) out 1000.

(** Each constructed prefix entry is the least legal year after its
    predecessor.  The source list may be longer than the constructed prefix. *)
Definition GreedyPrefix (years out : list Z) : Prop :=
  Zlength out <= Zlength years /\
  forall i, 0 <= i < Zlength out ->
    MinimalNext
      (Znth i years 0)
      (if Z.eq_dec i 0 then 1000 else Znth (i - 1) out 1000)
      (Znth i out 0).
