import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.euler_theorem_inverse.lean

open AUXLib

private abbrev residues (n : Int) : List Nat :=
  (List.range' 1 n.toNat).filter (fun k : Nat => Z.gcd (Int.ofNat k) n == 1)

def ModularPower (base exponent modulus result : Int) : Prop :=
  result = Z.modulo (Z.pow base exponent) modulus

def EulerTotientValue (n : Int) : Int := Int.ofNat (residues n).length

def EulerPhi (n result : Int) : Prop := result = EulerTotientValue n

def EulerTheoremInverse (value modulus inverse : Int) : Prop :=
  ∃ phi : Int, EulerPhi modulus phi ∧ ModularPower value (phi-1) modulus inverse ∧
    Z.modulo (value*inverse) modulus = 1

end Algorithms.euler_theorem_inverse.lean
