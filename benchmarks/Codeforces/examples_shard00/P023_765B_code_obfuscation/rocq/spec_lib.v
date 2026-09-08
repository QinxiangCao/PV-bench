Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition FirstOccurrence (s : list Z) (c i : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z =>
      0 <= candidate < Zlength s /\ Znth candidate s 0 = c)
    (fun candidate => candidate) i.

Definition ValidObfuscatedNames (s : list Z) : Prop :=
  Forall (fun c => 97 <= c <= 122) s /\
  forall c d j,
    97 <= c -> c < d -> d <= 122 ->
    FirstOccurrence s d j ->
    exists i, FirstOccurrence s c i /\ i < j.

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 500 /\
  Forall (fun c => 97 <= c <= 122) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> ValidObfuscatedNames s).
