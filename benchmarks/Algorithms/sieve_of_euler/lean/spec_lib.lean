import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.sieve_of_euler.lean

open AUXLib

def StrictPrime (p : Int) : Prop :=
  1 < p ∧
  ∀ d : Int,
    0 < d →
    Z.divide d p →
    d = 1 ∨ d = p

def LeastPrimeFactor (p k : Int) : Prop :=
  StrictPrime p ∧
  Z.divide p k ∧
  ∀ q : Int,
    StrictPrime q →
    Z.divide q k →
    p <= q

def FlagEntryFor (k value : Int) : Prop :=
  (StrictPrime k ∧ value = k) ∨
  (¬ StrictPrime k ∧ LeastPrimeFactor value k)

def LeastPrimeFlagList (n : Int) (flags : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  ∀ k : Int,
    2 <= k ∧ k <= n →
    FlagEntryFor k (Znth (k - 2) flags 0)

def PrimePrefixList (bound tot : Int) (primes : List Int) : Prop :=
  0 <= tot ∧
  (∀ pos : Int,
    1 <= pos ∧ pos <= tot →
    StrictPrime (Znth (pos - 1) primes 0) ∧
    Znth (pos - 1) primes 0 <= bound) ∧
  (∀ p : Int,
    2 <= p ∧ p <= bound →
    (StrictPrime p ↔
     ∃ pos : Int,
       1 <= pos ∧ pos <= tot ∧
       Znth (pos - 1) primes 0 = p)) ∧
  (∀ p q : Int,
    1 <= p ∧ p < q ∧ q <= tot →
    Znth (p - 1) primes 0 < Znth (q - 1) primes 0)

def EulerSieveResult
    (n tot : Int) (flags primes : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  Zlength primes = n ∧
  0 <= tot ∧ tot <= n ∧
  LeastPrimeFlagList n flags ∧
  PrimePrefixList n tot primes

end Algorithms.sieve_of_euler.lean
