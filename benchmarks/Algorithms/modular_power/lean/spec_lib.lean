import compcert.lib.ZArithCompat

namespace Algorithms.modular_power.lean

def ModularPower (base exponent modulus result : Int) : Prop :=
  result = Z.modulo (Z.pow base exponent) modulus

end Algorithms.modular_power.lean
