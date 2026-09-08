
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition NonzeroStartAt (a : list Z) (i : Z) : Prop :=
  0 <= i < Zlength a /\
  Znth i a 0 <> 0 /\
  (i = 0 \/ Znth (i - 1) a 0 = 0).

Definition PrefixRunCount (a : list Z) (upto runs : Z) : Prop :=
  exists starts : list Z,
    Zlength starts = runs /\
    NoDup starts /\
    forall i,
      In i starts <->
      0 <= i < upto /\ NonzeroStartAt a i.

Definition PrefixTailState (a : list Z) (upto inside : Z) : Prop :=
  (upto = 0 /\ inside = 0) \/
  (0 < upto <= Zlength a /\
   ((inside = 0 /\ Znth (upto - 1) a 0 = 0) \/
    (inside = 1 /\ Znth (upto - 1) a 0 <> 0))).

Definition ScanState (a : list Z) (upto runs inside : Z) : Prop :=
  PrefixRunCount a upto runs /\ PrefixTailState a upto inside.
