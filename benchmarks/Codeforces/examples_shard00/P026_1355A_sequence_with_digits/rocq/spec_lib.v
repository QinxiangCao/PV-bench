Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition DecimalDigitsOf (x : Z) (digits : list Z) : Prop :=
  0 < Zlength digits /\
  Forall (fun d => 0 <= d <= 9) digits /\
  Znth 0 digits 0 <> 0 /\
  x = fold_left (fun value digit => 10 * value + digit) digits 0.

Definition DigitRecurrenceStep (x y : Z) : Prop :=
  exists digits lo hi,
    DecimalDigitsOf x digits /\
    min_value_of_subset Z.le (fun d : Z => In d digits)
      (fun d => d) lo /\
    max_value_of_subset Z.le (fun d : Z => In d digits)
      (fun d => d) hi /\
    y = x + lo * hi.

Definition Pre (a1 k : Z) : Prop :=
  1 <= a1 <= 1000000000000000000 /\
  1 <= k <= 10000000000000000.

Definition Spec (a1 k out : Z) : Prop :=
  exists values,
    Zlength values = k /\ Znth 0 values 0 = a1 /\
    Znth (k - 1) values 0 = out /\
    forall i, 0 <= i < k - 1 ->
      DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0).
