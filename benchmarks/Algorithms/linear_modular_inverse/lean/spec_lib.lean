import compcert.lib.ZArithCompat
import AUXLib.ListLib

namespace Algorithms.linear_modular_inverse.lean

open AUXLib

def PrimeForLinearInverse (p : Int) : Prop :=
  2 ≤ p ∧ ∀ divisor, (2 ≤ divisor ∧ divisor < p) → Z.modulo p divisor ≠ 0

def CanonicalModularInverse (p index value : Int) : Prop :=
  (1 ≤ index ∧ index < p) ∧ (0 < value ∧ value < p) ∧
    ∃ coefficient, index * value + p * coefficient = 1

def ModularInversePrefix (p next : Int) (values : List Int) : Prop :=
  Zlength values = next - 1 ∧ ∀ index, (1 ≤ index ∧ index < next) →
    CanonicalModularInverse p index (Znth (index - 1) values 0)

end Algorithms.linear_modular_inverse.lean
