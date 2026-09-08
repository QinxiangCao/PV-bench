Require Import PVbench.Codeforces.examples_shard00.P052_1168A_increasing_by_modulo.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Feasible (m : Z) (a : list Z) (rounds : Z) : Prop :=
  exists b,
    ReachInRounds m rounds a b /\
    mono_nondec b.

Definition GreedyPrefixState
    (m : Z) (a : list Z) (rounds i last : Z) : Prop :=
  0 <= i <= Zlength a /\
  0 <= last < m /\
  ((i = 0 /\ last = 0) \/
   (0 < i /\
    exists b,
      ReachInRounds m rounds (sublist 0 i a) b /\
      mono_nondec b /\
      Zlength b = i /\
      Znth (i - 1) b 0 = last /\
      forall other,
        ReachInRounds m rounds (sublist 0 i a) other /\
        mono_nondec other ->
        last <= Znth (i - 1) other 0)).

Definition SearchState
    (m : Z) (a : list Z) (lo hi ans : Z) : Prop :=
  Feasible m a ans /\
  lo <= ans /\
  exists out,
    Spec m a out /\
    ((lo <= out <= hi) \/ out = ans).
