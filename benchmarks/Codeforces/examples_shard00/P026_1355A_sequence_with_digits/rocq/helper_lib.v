Require Import PVbench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition DigitExtrema (digits : list Z) (lo hi : Z) : Prop :=
  min_value_of_subset Z.le (fun d : Z => In d digits)
    (fun d => d) lo /\
  max_value_of_subset Z.le (fun d : Z => In d digits)
    (fun d => d) hi.

Definition DigitScanState
    (original remaining mn mx : Z) : Prop :=
  exists pending processed,
    DecimalDigitsOf original (pending ++ processed) /\
    remaining =
      fold_left (fun value digit => 10 * value + digit) pending 0 /\
    ((processed = nil /\ mn = 9 /\ mx = 0) \/
     (processed <> nil /\ DigitExtrema processed mn mx)).

Definition SequencePrefix (a1 count current : Z) : Prop :=
  exists values,
    Zlength values = count /\ Znth 0 values 0 = a1 /\
    Znth (count - 1) values 0 = current /\
    forall i, 0 <= i < count - 1 ->
      DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0).
