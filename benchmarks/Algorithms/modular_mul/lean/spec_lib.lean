import compcert.lib.ZArithCompat

namespace Algorithms.modular_mul.lean

def ModularMul (multiplicand multiplier modulus result : Int) : Prop :=
  (-modulus < result ∧ result < modulus) ∧
  ∃ quotient, multiplicand * multiplier = result + modulus * quotient

end Algorithms.modular_mul.lean
