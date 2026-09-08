Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Relations.Relation_Operators.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition OneSubsequenceAddition (before after : list Z) : Prop :=
  exists chosen prefix suffix,
    0 < Zlength before /\
    (exists i, 0 <= i < Zlength before /\ chosen i) /\
    before = prefix ++ suffix /\
    after = prefix ++
      [sum (fun i : Z => 0 <= i < Zlength before /\ chosen i)
         (fun i => Znth i before 0)] ++ suffix.

Definition Pre (final : list Z) : Prop :=
  1 <= Zlength final <= 200000 /\
  Forall (fun x => 1 <= x <= 200000) final.

Definition Spec (final : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> clos_refl_trans OneSubsequenceAddition [1] final).

Definition SortedAcceptance (sorted : list Z) : Prop :=
  0 < Zlength sorted /\
  Znth 0 sorted 0 = 1 /\
  forall i,
    1 <= i < Zlength sorted ->
    Znth i sorted 0 <= ListLib.sum (sublist 0 i sorted).

Definition FullDecisionSpecBridge
    (original sorted : list Z) : Prop :=
  forall out,
    Spec original out <->
      (out = 0 \/ out = 1) /\
      (out = 1 <-> SortedAcceptance sorted).
