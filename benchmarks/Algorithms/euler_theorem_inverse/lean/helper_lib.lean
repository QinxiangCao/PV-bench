import Algorithms.euler_theorem_inverse.lean.spec_lib

namespace Algorithms.euler_theorem_inverse.lean

open AUXLib

def EulerPhiResidual (original remaining result : Int) : Prop :=
  Z.divide remaining result ∧ ∀ original_phi remaining_phi : Int,
    EulerPhi original original_phi → EulerPhi remaining remaining_phi →
    original_phi*remaining = result*remaining_phi

def EulerPrime (p : Int) : Prop :=
  1<p ∧ ∀ d : Int, 0<d → Z.divide d p → d=1 ∨ d=p

def NoPrimeDivisorBelow (frontier remaining : Int) : Prop :=
  ∀ p : Int, EulerPrime p → p<frontier → ¬Z.divide p remaining

def EulerPhiProgress (original frontier remaining result : Int) : Prop :=
  EulerPhiResidual original remaining result ∧ NoPrimeDivisorBelow frontier remaining

def EulerPhiFactorCompletion (original factor current result : Int) : Prop :=
  ∀ terminal removed : Int, 0≤removed → current=terminal*Z.pow factor removed →
    Z.modulo terminal factor ≠ 0 → EulerPhiResidual original terminal (Z.div result factor*(factor-1))

def EulerPhiRemovalProgress (original factor current result : Int) : Prop :=
  ∃ before removed : Int, 0≤removed ∧ before=current*Z.pow factor removed ∧
    Z.divide factor before ∧ Z.divide factor result ∧
    EulerPhiProgress original factor before result ∧ EulerPhiFactorCompletion original factor current result

def EulerModularPowerProgress (original_base original_exponent modulus current_base remaining_exponent accumulator : Int) : Prop :=
  Z.modulo (accumulator*Z.pow current_base remaining_exponent) modulus = Z.modulo (Z.pow original_base original_exponent) modulus

end Algorithms.euler_theorem_inverse.lean
