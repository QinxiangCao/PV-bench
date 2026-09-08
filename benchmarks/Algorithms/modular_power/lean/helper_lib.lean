import Algorithms.modular_power.lean.spec_lib

namespace Algorithms.modular_power.lean

def ModularPowerProgress (original_base original_exponent modulus
    current_base remaining_exponent accumulator : Int) : Prop :=
  Z.modulo (accumulator * Z.pow current_base remaining_exponent) modulus =
    Z.modulo (Z.pow original_base original_exponent) modulus

end Algorithms.modular_power.lean
