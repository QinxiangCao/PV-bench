Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition ShirtSelection (score place : Z) : Prop :=
  exists values,
    Zlength values = 26 /\ Znth 0 values 0 = (score / 50) mod 475 /\
    (forall i, 0 <= i < 25 ->
       Znth (i + 1) values 0 = (Znth i values 0 * 96 + 42) mod 475) /\
    exists i, 1 <= i <= 25 /\ place = 26 + Znth i values 0.

Definition GoalWithHacks (p x y successful : Z) : Prop :=
  exists unsuccessful,
    0 <= unsuccessful /\
    y <= x + 100 * successful - 50 * unsuccessful /\
    ShirtSelection (x + 100 * successful - 50 * unsuccessful) p.

Definition Pre (p x y : Z) : Prop :=
  26 <= p <= 500 /\ 1 <= y <= x /\ x <= 20000 /\
  exists successful, 0 <= successful /\ GoalWithHacks p x y successful.

Definition Spec (p x y out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun successful : Z => 0 <= successful /\ GoalWithHacks p x y successful)
    (fun successful => successful) out.
