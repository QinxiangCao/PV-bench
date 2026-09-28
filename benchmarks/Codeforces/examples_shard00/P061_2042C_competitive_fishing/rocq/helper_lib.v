Require Export PVbench.Codeforces.examples_shard00.P061_2042C_competitive_fishing.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition FishingValue (c : Z) : Z :=
  if Z.eqb c 49 then 1 else -1.

Definition SuffixGain (f : list Z) (cut : Z) : Z :=
  fold_right Z.add 0
    (map FishingValue (sublist cut (Zlength f) f)).

Definition FishingGains (f : list Z) : list Z :=
  map (SuffixGain f) (Zrange 1 (Zlength f)).

Definition GainBuildState
    (f : list Z) (next : Z) (built : list Z) (current : Z) : Prop :=
  built = sublist next (Zlength f - 1) (FishingGains f) /\
  current = SuffixGain f next.

Definition PreparedGains (f gains : list Z) : Prop :=
  Permutation (FishingGains f) gains /\ ListLib.decreasing gains.

Definition GainSearchState
    (k : Z) (gains : list Z) (next prefix_sum : Z) : Prop :=
  prefix_sum = fold_right Z.add 0 (sublist 0 next gains) /\
  forall count,
    0 <= count <= next ->
    fold_right Z.add 0 (sublist 0 count gains) < k.

Definition FishingSearchResult
    (k : Z) (f gains : list Z) (out : Z) : Prop :=
  (out = -1 /\
   forall count,
     0 <= count <= Zlength gains ->
     fold_right Z.add 0 (sublist 0 count gains) < k) \/
  (2 <= out <= Zlength f /\
   k <= fold_right Z.add 0 (sublist 0 (out - 1) gains) /\
   forall count,
     0 <= count < out - 1 ->
     fold_right Z.add 0 (sublist 0 count gains) < k).

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.micromega.Psatz.
