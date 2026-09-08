import AUXLib.ListLib
import AUXLib.NumberTheory
import Algorithms.modular_mul.lean.spec_lib

namespace Algorithms.extended_chinese_remainder_theorem.lean

open AUXLib
export Algorithms.modular_mul.lean (ModularMul)

def CRTLCMPrefix (moduli : List Int) (count : Int) : Int :=
  (moduli.take count.toNat).foldl Z.lcm 1

def CRTCongruent (value residue modulus : Int) : Prop :=
  ∃ quotient, value = residue + modulus * quotient

def CRTAllCongruences (residues moduli : List Int) (count value : Int) : Prop :=
  ∀ index, (0 ≤ index ∧ index < count) →
    CRTCongruent value (Znth index residues 0) (Znth index moduli 0)

def ExtendedCRTInputs (residues moduli : List Int) (n : Int) : Prop :=
  1 ≤ n ∧ Zlength residues = n ∧ Zlength moduli = n ∧
  ∀ index, (0 ≤ index ∧ index < n) →
    (0 < Znth index moduli 0 ∧ Znth index moduli 0 ≤ 2147483647) ∧
    (0 ≤ Znth index residues 0 ∧ Znth index residues 0 < Znth index moduli 0)

def ExtendedCRTSystemCompatible (residues moduli : List Int) (n : Int) : Prop :=
  ∃ solution, CRTAllCongruences residues moduli n solution

def ExtendedCRTIntSafe (moduli : List Int) (n : Int) : Prop :=
  (∀ count, (1 ≤ count ∧ count ≤ n) → 0 < CRTLCMPrefix moduli count ∧ CRTLCMPrefix moduli count ≤ 2147483647) ∧
  (∀ index, (1 ≤ index ∧ index < n) →
    2 * Z.quot (Znth index moduli 0) (Z.gcd (CRTLCMPrefix moduli index) (Znth index moduli 0)) ≤ 2147483647)

def ExtendedCRTSystemResult (residues moduli : List Int) (n result combined_modulus : Int) : Prop :=
  combined_modulus = CRTLCMPrefix moduli n ∧ (0 ≤ result ∧ result < combined_modulus) ∧
  CRTAllCongruences residues moduli n result

end Algorithms.extended_chinese_remainder_theorem.lean
