
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Require Import Coq.Sorting.Permutation.

Require Import Coq.ZArith.Znumtheory.

Require Import AUXLib.ListLib.

Import ListNotations.

Definition MarkedBefore (bound value : Z) : Prop :=
  exists d, 2 <= d < bound /\ (d | value).

Definition PrimePrefixTable
    (bound : Z) (primes flags : list Z) : Prop :=
  2 <= bound <= 31624 /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < bound /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <-> ~ MarkedBefore bound k)).

Definition PrimeMarkTable
    (factor next : Z) (primes flags : list Z) : Prop :=
  2 <= factor <= 31623 /\
  factor * factor <= next /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < factor + 1 /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <->
        ~ (MarkedBefore factor k \/
           (factor | k) /\ factor * factor <= k < next))).

Definition CompletePrimeTable (primes : list Z) : Prop :=
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p <= 31623 /\ prime p).

Definition zdividesb (p x : Z) : bool :=
  if Zdivide_dec p x then true else false.

Definition PrimeFactorBagPrefix
    (a : list Z) (upto : Z) (factors : list Z) : Prop :=
  0 <= upto <= Zlength a /\
  Forall prime factors /\
  forall p, prime p ->
    Z.of_nat (count_occ Z.eq_dec factors p) =
    Z.of_nat
      (length
         (filter (zdividesb p) (firstn (Z.to_nat upto) a))).

Definition FactorScanState
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked,
    factors = done ++ picked /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested <= Zlength primes /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall p, prime p ->
       (In p picked <->
        In p (firstn (Z.to_nat tested) primes) /\
        (p | Znth index a 1))) /\
    (forall p,
       In p (firstn (Z.to_nat tested) primes) -> ~ (p | rem)).

Definition FactorDivideState
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked p,
    factors = done ++ picked ++ [p] /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested < Zlength primes /\
    p = Znth tested primes 0 /\
    prime p /\
    (p | Znth index a 1) /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall q, prime q ->
       (In q picked <->
        In q (firstn (Z.to_nat tested) primes) /\
        (q | Znth index a 1))) /\
    (forall q,
       In q (firstn (Z.to_nat tested) primes) -> ~ (q | rem)).

Definition DuplicatePrefixState
    (factors : list Z) (upto found : Z) : Prop :=
  0 <= upto <= Zlength factors /\
  (found = 0 \/ found = 1) /\
  (found = 1 <->
    exists i j,
      0 <= i < j /\ j < upto /\
      Znth i factors 0 = Znth j factors 0).

Definition ProperMarkedBefore (bound value : Z) : Prop :=
  exists d, 2 <= d < bound /\ d < value /\ (d | value).

Definition PrimePrefixTable2
    (bound : Z) (primes flags : list Z) : Prop :=
  2 <= bound <= 31624 /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < bound /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <-> ~ ProperMarkedBefore bound k)).

Definition PrimeMarkTable2
    (factor next : Z) (primes flags : list Z) : Prop :=
  2 <= factor <= 31623 /\
  factor * factor <= next /\
  (factor | next) /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < factor + 1 /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <->
        ~ (ProperMarkedBefore factor k \/
           (factor | k) /\ factor * factor <= k < next))).

Definition FactorAppendCapacity
    (primes : list Z) (index tested rem count : Z) : Prop :=
  (0 <= tested < Zlength primes /\ (Znth tested primes 0 | rem)) ->
  count + 1 <= index * 10 + 9.

Definition DuplicateScanLoopState
    (factors : list Z) (count cursor found : Z) : Prop :=
  (count = 0 /\ cursor = 1 /\ DuplicatePrefixState factors 0 found) \/
  (1 <= count /\ 1 <= cursor <= count /\
   DuplicatePrefixState factors cursor found).

Definition ResidualPrimeCoverage
    (original rem : Z) (picked : list Z) : Prop :=
  forall p, prime p ->
    ((p | original) <-> In p picked \/ (p | rem)).

Definition FactorScanState2
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked,
    factors = done ++ picked /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested <= Zlength primes /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall p, prime p ->
       (In p picked <->
        In p (firstn (Z.to_nat tested) primes) /\
        (p | Znth index a 1))) /\
    (forall p,
       In p (firstn (Z.to_nat tested) primes) -> ~ (p | rem)) /\
    ResidualPrimeCoverage (Znth index a 1) rem picked.

Definition FactorDivideState2
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked p,
    factors = done ++ picked ++ [p] /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested < Zlength primes /\
    p = Znth tested primes 0 /\
    prime p /\
    (p | Znth index a 1) /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall q, prime q ->
       (In q picked <->
        In q (firstn (Z.to_nat tested) primes) /\
        (q | Znth index a 1))) /\
    (forall q,
       In q (firstn (Z.to_nat tested) primes) -> ~ (q | rem)) /\
    ResidualPrimeCoverage (Znth index a 1) rem (picked ++ [p]).
