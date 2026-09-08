Require Import PVbench.Codeforces.examples_shard00.P037_1875C_jellyfish_and_green_apple.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition GcdValue (a b : Z) : Z := Z.gcd a b.

Definition PowerOfTwo (x : Z) : Prop :=
  exists k, 0 <= k /\ x = 2 ^ k.

Definition DyadicResidue (start modulus i : Z) : Z :=
  (2 ^ i * start) mod modulus.

Definition DyadicRemainderPrefix
    (start modulus current total : Z) : Prop :=
  exists k,
    0 <= k /\
    current = DyadicResidue start modulus k /\
    total = fold_right Z.add 0
              (Zmap_range (fun i => DyadicResidue start modulus i) k).
