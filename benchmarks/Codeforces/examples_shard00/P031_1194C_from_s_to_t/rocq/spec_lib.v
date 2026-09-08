Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CanInsertFromPool (s p t : list Z) : Prop :=
  exists inserted,
    (exists unused, Permutation p (inserted ++ unused)) /\
    exists positions,
      Zlength positions = Zlength s /\
      (forall i, 0 <= i < Zlength s ->
         0 <= Znth i positions 0 < Zlength t /\
         Znth (Znth i positions 0) t 0 = Znth i s 0) /\
      mono_inc positions /\
      Permutation (s ++ inserted) t.

Definition Pre (s t p : list Z) : Prop :=
  1 <= Zlength s <= 100 /\ 1 <= Zlength t <= 100 /\ 1 <= Zlength p <= 100 /\
  Forall (fun c => 97 <= c <= 122) s /\
  Forall (fun c => 97 <= c <= 122) t /\
  Forall (fun c => 97 <= c <= 122) p.

Definition Spec (s t p : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> CanInsertFromPool s p t).
