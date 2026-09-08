Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P060_1930D1_sum_over_all_substrings.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* A mathematical summary of the substring rows whose left endpoints have
   already been processed.  The witness is intentionally hidden behind this
   predicate so that the C invariant talks about completed rows, rather than
   about updates to a higher-order function. *)
Definition CompletedRows (s : list Z) (upto total : Z) : Prop :=
  exists f : Z -> Z -> Z,
    (forall i j,
       0 <= i < upto -> i < j <= Zlength s ->
       FValue (sublist i j s) (f i j)) /\
    total =
      sum_range 0 (upto - 1)
        (fun i => sum_range (i + 1) (Zlength s) (fun j => f i j)).

(* The already visited right endpoints in one fixed-left-endpoint row. *)
Definition CurrentRow
    (s : list Z) (left upto row_total : Z) : Prop :=
  exists f : Z -> Z,
    (forall right,
       left < right <= upto ->
       FValue (sublist left right s) (f right)) /\
    row_total = sum_range (left + 1) upto f.

Fixpoint ThreeSeparated (positions : list Z) : Prop :=
  match positions with
  | nil => True
  | x :: rest =>
      Forall (fun y => x + 3 <= y) rest /\ ThreeSeparated rest
  end.

Definition CoveredBy (positions : list Z) (q : Z) : Prop :=
  exists p, In p positions /\ p <= q <= p + 2.

(* [positions] is a minimum-cardinality set of binary-one positions whose
   length-three rightward intervals cover every one in the visited prefix.
   This is an implementation-independent packing/covering property; [cover]
   merely exposes the right frontier needed by the next C step. *)
Definition PrefixCoverSummary
    (s : list Z) (left upto cover count : Z) : Prop :=
  left <= upto <= Zlength s /\
  exists positions : list Z,
    Zlength positions = count /\
    Forall
      (fun p => left <= p < upto /\ Znth p s 0 = 49)
      positions /\
    ThreeSeparated positions /\
    (forall q,
       left <= q < upto -> Znth q s 0 = 49 -> CoveredBy positions q) /\
    ((positions = nil /\ cover = left - 1) \/
     exists prefix last,
       positions = prefix ++ last :: nil /\ cover = last + 2) /\
    (left < upto -> FValue (sublist left upto s) count).
