Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition OneXorMerge (a b : list Z) : Prop :=
  exists i, 0 <= i < Zlength a - 1 /\
    b = sublist 0 i a ++
      (Z.lxor (Znth i a 0) (Znth (i + 1) a 0)) ::
      sublist (i + 2) (Zlength a) a.

Definition DestroyTrace (a : list Z) (m : Z) : Prop :=
  exists states, Zlength states = m + 1 /\ Znth 0 states nil = a /\
    (forall i, 0 <= i < m ->
      OneXorMerge (Znth i states nil) (Znth (i + 1) states nil)) /\
    exists i, 0 <= i < Zlength (Znth m states nil) - 1 /\
      Znth i (Znth m states nil) 0 > Znth (i + 1) (Znth m states nil) 0.

Definition Pre (a : list Z) : Prop :=
  2 <= Zlength a <= 100000 /\
  Forall (fun x => 1 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = -1 /\ forall m, ~ DestroyTrace a m) \/
  min_value_of_subset Z.le (DestroyTrace a) (fun moves => moves) out.

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.micromega.Psatz.

Require Import Coq.Arith.Wf_nat.
