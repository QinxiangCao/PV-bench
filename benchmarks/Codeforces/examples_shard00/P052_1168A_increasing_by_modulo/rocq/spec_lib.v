Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ReachInRounds (m rounds : Z) (a b : list Z) : Prop :=
  Forall2 (fun before after =>
    exists inc, 0 <= inc <= rounds /\
      after = (before + inc) mod m) a b.

Definition Pre (m : Z) (a : list Z) : Prop :=
  1 <= m <= 300000 /\
  1 <= Zlength a <= 300000 /\
  Forall (fun x => 0 <= x < m) a.

Definition Spec (m : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z * list Z =>
      ReachInRounds m (fst candidate) a (snd candidate) /\
      mono_nondec (snd candidate))
    fst out.
