Require Export PVbench.Algorithms.sieve_of_euler.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Znumtheory Coq.ZArith.Wf_Z MaxMinLib.MaxMin SetsClass.SetsClass AUXLib.MonotonicList Coq.Setoids.Setoid.

Module Legacy.
Include PVbench.Algorithms.sieve_of_euler.rocq.spec_lib.Legacy.
Definition ProductIndex
    (current j : Z) (primes : list Z) : Z :=
  current * Znth (j - 1) primes 0.

Definition FlagValue (flags : list Z) (k : Z) : Z :=
  Znth (k - 2) flags 0.
End Legacy.

Module Modern.
Import Legacy.
Include PVbench.Algorithms.sieve_of_euler.rocq.spec_lib.Modern.
Definition ProductIndex := Legacy.ProductIndex.

Definition FlagValue := Legacy.FlagValue.

Definition LeastPrimeFactor (p k : Z) : Prop :=
  min_value_of_subset Z.le (fun q => StrictPrime q /\ Z.divide q k)
    (fun q : Z => q) p.

Definition FlagEntryFor (k value : Z) : Prop :=
  (StrictPrime k /\ value = k) \/
  (~ StrictPrime k /\ LeastPrimeFactor value k).

Definition LeastPrimeFlagList (n : Z) (flags : list Z) : Prop :=
  forall k : Z,
    2 <= k /\ k <= n ->
    FlagEntryFor k (Znth (k - 2) flags 0).

Definition PriorNonDivisibility
    (current j : Z) (primes : list Z) : Prop :=
  Forall (fun p => ~ Z.divide p current) (sublist 0 (j - 1) primes).

Definition CurrentProductMarked
    (n current pos : Z) (flags primes : list Z) : Prop :=
  2 <= ProductIndex current pos primes /\
  ProductIndex current pos primes <= n ->
  FlagValue flags (ProductIndex current pos primes) =
    Znth (pos - 1) primes 0 /\
  FlagValue flags (ProductIndex current pos primes) <>
    ProductIndex current pos primes /\
  FlagEntryFor (ProductIndex current pos primes)
    (FlagValue flags (ProductIndex current pos primes)).

Definition CurrentBaseProgress
    (n current j : Z) (flags primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos < j ->
    CurrentProductMarked n current pos flags primes.

Definition EarlierLinearProduct
    (frontier k tot : Z) (primes : list Z) : Prop :=
  exists base pos : Z,
    2 <= base /\ base < frontier /\
    1 <= pos /\ pos <= tot /\
    Znth (pos - 1) primes 0 <= base /\
    PriorNonDivisibility base pos primes /\
    k = base * Znth (pos - 1) primes 0.

Definition FutureSelfCompleteness
    (frontier k tot : Z) (primes : list Z) : Prop :=
  ~ EarlierLinearProduct frontier k tot primes.

Definition FutureFlagState
    (frontier k tot : Z) (flags primes : list Z) : Prop :=
  (FlagValue flags k <> k -> FlagEntryFor k (FlagValue flags k)) /\
  (FlagValue flags k = k -> FutureSelfCompleteness frontier k tot primes).

Definition EulerFlagState
    (n frontier tot : Z) (flags primes : list Z) : Prop :=
  forall k : Z,
    2 <= k /\ k <= n ->
    (k <= frontier -> FlagEntryFor k (FlagValue flags k)) /\
    (frontier < k -> FutureFlagState frontier k tot flags primes).

Definition EulerSieveResult
    (n tot : Z) (flags primes : list Z) : Prop :=
  LeastPrimeFlagList n flags /\
  PrimePrefixList n tot primes.

Definition EulerInitPrefix (n next : Z) (flags : list Z) : Prop :=
  forall k : Z,
    2 <= k /\ k < next ->
    Znth (k - 2) flags 0 = k.

Definition EulerOuterState
    (n next tot : Z) (flags primes : list Z) : Prop :=
  EulerFlagState n next tot flags primes /\
  PrimePrefixList (next - 1) tot primes.

Definition EulerInnerState
    (n current j tot : Z) (flags primes : list Z) : Prop :=
  EulerFlagState n current tot flags primes /\
  PrimePrefixList current tot primes /\
  CurrentBaseProgress n current j flags primes /\
  PriorNonDivisibility current j primes /\
  (ProductIndex current j primes > n ->
   EulerOuterState n (current + 1) tot flags primes).

Definition EulerInnerMarkedState
    (n current j tot : Z) (flags primes : list Z) : Prop :=
  EulerInnerState n current j tot flags primes /\
  FlagEntryFor (ProductIndex current j primes)
    (Znth (j - 1) primes 0) /\
  FlagValue flags (ProductIndex current j primes) =
    Znth (j - 1) primes 0 /\
  CurrentBaseProgress n current (j + 1) flags primes /\
  (Z.divide (Znth (j - 1) primes 0) current ->
   EulerOuterState n (current + 1) tot flags primes) /\
  (~ Z.divide (Znth (j - 1) primes 0) current ->
   EulerInnerState n current (j + 1) tot flags primes).
End Modern.

Export Legacy Modern.
