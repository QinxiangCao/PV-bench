Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.ZArith.Znumtheory.
Require Import PVbench.Codeforces.examples_shard01.P019_1787B_number_factorization.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.


(* A mathematical prime/exponent profile.  The definitions below expose the
   three stable states used by the implementation: a partially extracted
   prime factorisation, the maximum exponent, and the sum of square-free
   exponent layers.  They describe the number-theoretic objects rather than
   replaying the C control flow. *)
Definition FactorPower (ps es : list Z) : Z :=
  fold_right Z.mul 1
    (map (fun i => Z.pow (Znth i ps 1) (Znth i es 0))
         (Zrange 0 (Zlength ps))).

Definition PrimeExponentProfile (ps es : list Z) : Prop :=
  Zlength ps = Zlength es /\
  NoDup ps /\
  Forall prime ps /\
  (forall i, 0 <= i < Zlength es -> 1 <= Znth i es 0 <= 30).

Definition FactorScan
    (orig rem next : Z) (ps es : list Z) : Prop :=
  2 <= orig <= 1000000000 /\
  1 <= rem <= orig /\
  2 <= next <= orig /\
  Zlength ps <= 29 /\
  PrimeExponentProfile ps es /\
  Forall (fun p => 2 <= p < next) ps /\
  orig = rem * FactorPower ps es /\
  (forall p, prime p -> 2 <= p < next -> ~ (p | rem)).

Definition FactorExtract
    (orig rem d : Z) (ps es : list Z) (e : Z) : Prop :=
  2 <= orig <= 1000000000 /\
  1 <= rem <= orig /\
  2 <= d <= orig /\
  Zlength ps <= 29 /\
  PrimeExponentProfile ps es /\
  Forall (fun p => 2 <= p < d) ps /\
  prime d /\
  0 <= e <= 30 /\
  orig = rem * Z.pow d e * FactorPower ps es /\
  (forall p, prime p -> 2 <= p < d -> ~ (p | rem)) /\
  (e = 0 -> (d | rem)).

Definition PrimeFactorization (orig : Z) (ps es : list Z) : Prop :=
  2 <= orig <= 1000000000 /\
  Zlength ps <= 30 /\
  PrimeExponentProfile ps es /\
  orig = FactorPower ps es.

Definition PrefixMaximum (es : list Z) (upto mx : Z) : Prop :=
  0 <= upto <= Zlength es /\
  0 <= mx <= 30 /\
  (forall i, 0 <= i < upto -> Znth i es 0 <= mx) /\
  (upto = 0 -> mx = 0) /\
  (0 < upto -> exists i, 0 <= i < upto /\ Znth i es 0 = mx).

Definition MaximumExponent (es : list Z) (mx : Z) : Prop :=
  PrefixMaximum es (Zlength es) mx.

Definition LayerPrefixValue
    (ps es : list Z) (k upto : Z) : Z :=
  fold_right Z.mul 1
    (map
       (fun i =>
          if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
       (Zrange 0 upto)).

Definition LayerValue (ps es : list Z) (k : Z) : Z :=
  LayerPrefixValue ps es k (Zlength ps).

Definition LayerProductPrefix
    (orig : Z) (ps es : list Z) (k upto prod : Z) : Prop :=
  PrimeFactorization orig ps es /\
  1 <= k <= 30 /\
  0 <= upto <= Zlength ps /\
  prod = LayerPrefixValue ps es k upto /\
  1 <= prod <= orig /\
  (forall i,
      upto <= i < Zlength ps ->
      k <= Znth i es 0 ->
      prod * Znth i ps 1 <= orig).

Definition LayerSumPrefix
    (orig : Z) (ps es : list Z) (mx next total : Z) : Prop :=
  PrimeFactorization orig ps es /\
  MaximumExponent es mx /\
  1 <= next <= mx + 1 /\
  total = sum_range 1 (next - 1) (LayerValue ps es) /\
  0 <= total <= orig /\
  (next <= mx -> total + LayerValue ps es next <= orig).

Definition FactorizationAnswer
    (orig : Z) (ps es : list Z) (total : Z) : Prop :=
  PrimeFactorization orig ps es /\
  exists mx,
    MaximumExponent es mx /\
    total = sum_range 1 mx (LayerValue ps es) /\
    0 <= total <= orig.

Definition ExtractionScale (rem d e : Z) : Prop :=
  d * d <= rem * Z.pow d e.

(* Asserted by the T2 annotations at the point where the factorisation and the
   maximum exponent are both established; its proof is T3 material. *)
Definition LayerOptimalityCertificate
    (orig : Z) (ps es : list Z) (mx : Z) : Prop :=
  Spec orig (sum_range 1 mx (LayerValue ps es)).
