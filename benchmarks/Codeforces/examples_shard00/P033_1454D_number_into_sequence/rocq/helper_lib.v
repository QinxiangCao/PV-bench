Require Import PVbench.Codeforces.examples_shard00.P033_1454D_number_into_sequence.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition FactorSearchState
    (n value p best_prime best_exp : Z) : Prop :=
  2 <= n <= 10000000000 /\
  1 <= value <= n /\
  2 <= p <= 100001 /\
  p * p <= 1000000000000000000 /\
  1 <= best_exp <= 64 /\
  2 <= best_prime <= n /\
  Z.divide value n /\
  Z.divide (Z.pow best_prime best_exp) n /\
  (forall q k,
      2 <= q < p ->
      1 <= k ->
      Z.divide (Z.pow q k) n ->
      k <= best_exp).

Definition FactorExtractState
    (n value p e best_prime best_exp : Z) : Prop :=
  2 <= n <= 10000000000 /\
  1 <= value <= n /\
  2 <= p <= 100001 /\
  0 <= e <= 64 /\
  1 <= best_exp <= 64 /\
  2 <= best_prime <= n /\
  Z.divide (value * Z.pow p e) n /\
  Z.divide (Z.pow best_prime best_exp) n.

Definition BestPowerChoice (n best_prime best_exp : Z) : Prop :=
  2 <= n <= 10000000000 /\
  1 <= best_exp <= 64 /\
  2 <= best_prime <= n /\
  exists result,
    Zlength result = best_exp /\
    (forall i, 0 <= i < best_exp - 1 -> Znth i result 0 = best_prime) /\
    ValidFactorSequence n result /\
    Spec n result.

Definition OutputPrefixState
    (n best_prime best_exp i rest : Z) (written : list Z) : Prop :=
  BestPowerChoice n best_prime best_exp /\
  0 <= i < best_exp /\
  1 <= rest <= n /\
  Zlength written = i /\
  (forall j, 0 <= j < i -> Znth j written 0 = best_prime) /\
  rest * Z.pow best_prime i = n.

Definition FinalOutputSequence
    (n best_prime best_exp rest : Z) (result : list Z) : Prop :=
  BestPowerChoice n best_prime best_exp /\
  1 <= rest <= n /\
  Zlength result = best_exp /\
  (forall j, 0 <= j < best_exp - 1 -> Znth j result 0 = best_prime) /\
  Znth (best_exp - 1) result 0 = rest /\
  rest * Z.pow best_prime (best_exp - 1) = n /\
  Spec n result.

Require Import Coq.Sorting.Permutation.

Require Import Coq.ZArith.Znumtheory.

Import ListNotations.

Definition FactorProfileProduct (ps es : list Z) : Z :=
  fold_right Z.mul 1
    (map (fun i => Z.pow (Znth i ps 1) (Znth i es 0))
         (Zrange 0 (Zlength ps))).

Definition FactorProfileShape (p : Z) (ps es : list Z) : Prop :=
  Zlength ps = Zlength es /\
  NoDup ps /\
  Forall prime ps /\
  (forall i, 0 <= i < Zlength ps -> 2 <= Znth i ps 1 < p) /\
  (forall i, 0 <= i < Zlength es -> 1 <= Znth i es 0 <= 64).

Definition FactorSearchProfile
    (n value p best_prime best_exp : Z) (ps es : list Z) : Prop :=
  FactorSearchState n value p best_prime best_exp /\
  FactorProfileShape p ps es /\
  n = value * FactorProfileProduct ps es /\
  (forall q, 2 <= q < p -> ~ Z.divide q value) /\
  (forall i, 0 <= i < Zlength es -> Znth i es 0 <= best_exp) /\
  (best_exp = 1 \/
    exists i, 0 <= i < Zlength es /\ Znth i ps 1 = best_prime /\
      Znth i es 0 = best_exp) /\
  (forall q k,
      p <= q ->
      1 <= k ->
      Z.divide (Z.pow q k) n ->
      k <= best_exp \/ Z.divide (Z.pow q k) value) /\
  (value mod p <> 0 ->
    forall k, 1 <= k -> Z.divide (Z.pow p k) n -> k <= best_exp) /\
  (value mod p <> 0 -> p + 1 <= 100001) /\
  (p * p > value -> BestPowerChoice n best_prime best_exp).

Definition FactorExtractOrigin
    (n value p e best_prime best_exp : Z) (ps es : list Z) : Prop :=
  prime p /\
  FactorSearchProfile n (value * Z.pow p e) p best_prime best_exp ps es.

Definition FactorExtractGuard (value p e : Z) : Prop :=
  p * p <= value * Z.pow p e.

Definition FactorExtractProfile
    (n value p e best_prime best_exp : Z) (ps es : list Z) : Prop :=
  FactorExtractState n value p e best_prime best_exp /\
  FactorExtractOrigin n value p e best_prime best_exp ps es /\
  FactorProfileShape p ps es /\
  n = value * Z.pow p e * FactorProfileProduct ps es /\
  (forall i, 0 <= i < Zlength es -> Znth i es 0 <= best_exp) /\
  (best_exp = 1 \/
    exists i, 0 <= i < Zlength es /\ Znth i ps 1 = best_prime /\
      Znth i es 0 = best_exp) /\
  (value mod p <> 0 -> p <= n) /\
  (value mod p <> 0 -> p + 1 <= 100001) /\
  (value mod p <> 0 ->
    e > best_exp ->
    FactorSearchProfile n value (p + 1) p e (ps ++ [p]) (es ++ [e])) /\
  (value mod p <> 0 ->
    e <= best_exp ->
    FactorSearchProfile n value (p + 1) best_prime best_exp
      (ps ++ [p]) (es ++ [e])).
