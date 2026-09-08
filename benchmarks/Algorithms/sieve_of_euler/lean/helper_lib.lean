import Algorithms.sieve_of_euler.lean.spec_lib

namespace Algorithms.sieve_of_euler.lean

open AUXLib

def PrimeBounds (n tot : Int) (primes : List Int) : Prop :=
  ∀ pos : Int,
    1 <= pos ∧ pos <= tot →
    2 <= Znth (pos - 1) primes 0 ∧
    Znth (pos - 1) primes 0 <= n

def PriorNonDivisibility
    (current j : Int) (primes : List Int) : Prop :=
  ∀ pos : Int,
    1 <= pos ∧ pos < j →
    ¬ Z.divide (Znth (pos - 1) primes 0) current

def ProductIndex
    (current j : Int) (primes : List Int) : Int :=
  current * Znth (j - 1) primes 0

def FlagValue (flags : List Int) (k : Int) : Int :=
  Znth (k - 2) flags 0

def CurrentProductMarked
    (n current pos : Int) (flags primes : List Int) : Prop :=
  2 <= ProductIndex current pos primes ∧
  ProductIndex current pos primes <= n →
  FlagValue flags (ProductIndex current pos primes) =
    Znth (pos - 1) primes 0 ∧
  FlagValue flags (ProductIndex current pos primes) ≠
    ProductIndex current pos primes ∧
  FlagEntryFor (ProductIndex current pos primes)
    (FlagValue flags (ProductIndex current pos primes))

def CurrentBaseProgress
    (n current j : Int) (flags primes : List Int) : Prop :=
  ∀ pos : Int,
    1 <= pos ∧ pos < j →
    CurrentProductMarked n current pos flags primes

def EarlierLinearProduct
    (frontier k tot : Int) (primes : List Int) : Prop :=
  ∃ base pos : Int,
    2 <= base ∧ base < frontier ∧
    1 <= pos ∧ pos <= tot ∧
    Znth (pos - 1) primes 0 <= base ∧
    PriorNonDivisibility base pos primes ∧
    k = base * Znth (pos - 1) primes 0

def FutureSelfCompleteness
    (frontier k tot : Int) (primes : List Int) : Prop :=
  ¬ EarlierLinearProduct frontier k tot primes

def FutureFlagState
    (frontier k tot : Int) (flags primes : List Int) : Prop :=
  (FlagValue flags k ≠ k → FlagEntryFor k (FlagValue flags k)) ∧
  (FlagValue flags k = k → FutureSelfCompleteness frontier k tot primes)

def EulerFlagState
    (n frontier tot : Int) (flags primes : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  ∀ k : Int,
    2 <= k ∧ k <= n →
    (k <= frontier → FlagEntryFor k (FlagValue flags k)) ∧
    (frontier < k → FutureFlagState frontier k tot flags primes)

def EulerInitPrefix (n next : Int) (flags : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  ∀ k : Int,
    2 <= k ∧ k < next →
    Znth (k - 2) flags 0 = k

def EulerOuterState
    (n next tot : Int) (flags primes : List Int) : Prop :=
  EulerFlagState n next tot flags primes ∧
  Zlength primes = n ∧
  2 <= next ∧ next <= n + 1 ∧
  0 <= tot ∧ tot < next ∧
  PrimePrefixList (next - 1) tot primes ∧
  PrimeBounds n tot primes

def EulerInnerState
    (n current j tot : Int) (flags primes : List Int) : Prop :=
  EulerFlagState n current tot flags primes ∧
  Zlength primes = n ∧
  2 <= current ∧ current <= n ∧
  1 <= j ∧ j <= tot ∧
  0 < tot ∧ tot <= n ∧
  tot < current + 1 ∧
  PrimePrefixList current tot primes ∧
  PrimeBounds current tot primes ∧
  CurrentBaseProgress n current j flags primes ∧
  PriorNonDivisibility current j primes ∧
  (ProductIndex current j primes > n →
   EulerOuterState n (current + 1) tot flags primes)

def EulerInnerMarkedState
    (n current j tot : Int) (flags primes : List Int) : Prop :=
  EulerInnerState n current j tot flags primes ∧
  ProductIndex current j primes <= n ∧
  FlagEntryFor (ProductIndex current j primes)
    (Znth (j - 1) primes 0) ∧
  FlagValue flags (ProductIndex current j primes) =
    Znth (j - 1) primes 0 ∧
  CurrentBaseProgress n current (j + 1) flags primes ∧
  (Z.divide (Znth (j - 1) primes 0) current →
   EulerOuterState n (current + 1) tot flags primes) ∧
  (¬ Z.divide (Znth (j - 1) primes 0) current →
   EulerInnerState n current (j + 1) tot flags primes)

end Algorithms.sieve_of_euler.lean
