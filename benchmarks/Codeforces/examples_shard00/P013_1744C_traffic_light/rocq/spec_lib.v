Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition WaitsUntilGreen (s : list Z) (start wait : Z) : Prop :=
  0 <= start < Zlength s /\
  min_value_of_subset Z.le
    (fun candidate : Z =>
      0 <= candidate < Zlength s /\
      Znth ((start + candidate) mod Zlength s) s 0 = 103)
    (fun candidate => candidate) wait.

Definition Pre (current : Z) (s : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\
  (current = 114 \/ current = 121 \/ current = 103) /\
  Forall (fun c => c = 114 \/ c = 121 \/ c = 103) s /\
  In 103 s /\ In current s.

Definition Spec (current : Z) (s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : Z * Z =>
      Znth (fst candidate) s 0 = current /\
      WaitsUntilGreen s (fst candidate) (snd candidate))
    snd out.
