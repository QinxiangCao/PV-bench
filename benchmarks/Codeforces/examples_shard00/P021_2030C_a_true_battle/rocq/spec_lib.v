Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition HasAdjacentOnes (values : list Z) : Prop :=
  exists i,
    0 <= i /\
    i + 1 < Zlength values /\
    Znth i values 0 = 49 /\
    Znth (i + 1) values 0 = 49.

Definition WinningCriterion (values : list Z) : Prop :=
  Znth 0 values 0 = 49 \/
  Znth (Zlength values - 1) values 0 = 49 \/
  HasAdjacentOnes values.

Definition Pre (values : list Z) : Prop :=
  2 <= Zlength values <= 200000 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun c => c = 48 \/ c = 49) values.

Definition Spec (values : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> WinningCriterion values).
