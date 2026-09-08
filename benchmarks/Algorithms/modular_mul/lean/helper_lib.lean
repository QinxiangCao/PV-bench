import Algorithms.modular_mul.lean.spec_lib

namespace Algorithms.modular_mul.lean

def ModularMulProgress (original_multiplicand original_multiplier modulus
    current_multiplicand remaining_multiplier accumulator sign : Int) : Prop :=
  ∃ quotient, original_multiplicand * original_multiplier =
    sign * (accumulator + current_multiplicand * remaining_multiplier) + modulus * quotient

end Algorithms.modular_mul.lean
