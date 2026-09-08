Require Import PVbench.Codeforces.examples_shard00.P023_765B_code_obfuscation.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ObfuscationPrefixState (s : list Z) (processed next : Z) : Prop :=
  0 <= processed <= Zlength s /\
  97 <= next <= 122 /\
  (forall c d j,
     97 <= c -> c < d -> d <= 122 ->
     FirstOccurrence s d j -> j < processed ->
     exists k, FirstOccurrence s c k /\ k < j) /\
  (forall k, 0 <= k < processed -> Znth k s 0 <= next) /\
  (forall c, 97 <= c < next ->
     exists k, FirstOccurrence s c k /\ k < processed) /\
  (next < 122 ->
     forall k, 0 <= k < processed -> Znth k s 0 <> next).
