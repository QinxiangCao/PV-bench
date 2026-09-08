import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.chinese_remainder_theorem.lean

open AUXLib

def CRTProduct (moduli : List Int) : Int := moduli.foldr (· * ·) 1

def CRTInputValid (remainders moduli : List Int) : Prop :=
  Zlength remainders = Zlength moduli ∧ 1 ≤ Zlength moduli ∧
  (∀ i, (0 ≤ i ∧ i < Zlength moduli) →
    1 ≤ Znth i moduli 0 ∧ 0 ≤ Znth i remainders 0 ∧ Znth i remainders 0 < Znth i moduli 0) ∧
  (∀ i j, (0 ≤ i ∧ i < j ∧ j < Zlength moduli) → Z.gcd (Znth i moduli 0) (Znth j moduli 0) = 1)

def CRTMachineSafe (remainders moduli : List Int) : Prop :=
  let product := CRTProduct moduli
  (1 ≤ product ∧ product ≤ 46340) ∧
  (∀ i coefficient, (0 ≤ i ∧ i < Zlength moduli) →
    (-2147483648 ≤ coefficient ∧ coefficient ≤ 2147483647) →
    -2147483648 ≤ coefficient * Z.div product (Znth i moduli 0) ∧
    coefficient * Z.div product (Znth i moduli 0) ≤ 2147483647)

def CanonicalCRTSolution (remainders moduli : List Int) (answer : Int) : Prop :=
  (0 ≤ answer ∧ answer < CRTProduct moduli) ∧
  ∀ i, (0 ≤ i ∧ i < Zlength moduli) → Z.modulo answer (Znth i moduli 0) = Znth i remainders 0

end Algorithms.chinese_remainder_theorem.lean
