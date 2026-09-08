Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Pre (a : list Z) : Prop := 2 <= Zlength a <= 100000 /\ Forall (fun x => 1 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <->
    exists i j x, 0 <= i < Zlength a /\ 0 <= j < Zlength a /\ i <> j /\ x >= 2 /\
      (x | Znth i a 0) /\ (x | Znth j a 0)).




Import ListNotations.
