import Algorithms.lucas_theorem.lean.spec_lib

namespace Algorithms.lucas_theorem.lean

open AUXLib

def BinomialDigitResidue (upper lower p result : Int) : Prop := result=Z.modulo (LucasBinomialCoefficient upper lower) p

def DigitProductProgress (upper lower p next numerator denominator : Int) : Prop :=
  numerator=Z.modulo (DigitNumeratorPrefix upper lower (next-1)) p ∧ denominator=Z.modulo (DigitDenominatorPrefix (next-1)) p

def LucasProgress (original_upper original_lower p current_upper current_lower result : Int) : Prop :=
  ∃ processed : Nat,current_upper=Z.div original_upper (Z.pow p (Int.ofNat processed)) ∧
    current_lower=Z.div original_lower (Z.pow p (Int.ofNat processed)) ∧ result=LucasPrefixProduct original_upper original_lower p processed ∧
    Z.modulo (LucasBinomialCoefficient original_upper original_lower) p=Z.modulo (result*LucasBinomialCoefficient current_upper current_lower) p

end Algorithms.lucas_theorem.lean
