import AUXLib.Prime

namespace Algorithms.lucas_theorem.lean

open AUXLib

def ModularPower (base exponent modulus result : Int) : Prop := result=Z.modulo (Z.pow base exponent) modulus

def PrimeForLucas (p : Int) : Prop :=
  2≤p ∧ ∀ divisor : Int, 2≤divisor ∧ divisor<p → Z.modulo p divisor≠0

def LucasNatBinomial : Nat → Nat → Nat
  | _,0 => 1
  | 0,_+1 => 0
  | n+1,k+1 => LucasNatBinomial n k+LucasNatBinomial n (k+1)

def LucasBinomialCoefficient (upper lower : Int) : Int := Int.ofNat (LucasNatBinomial upper.toNat lower.toNat)

def LucasBinomialResidue (n m p result : Int) : Prop := result=Z.modulo (LucasBinomialCoefficient (n+m) n) p

def DigitEffectiveLower (upper lower : Int) : Int := min lower (upper-lower)

def LucasRangeProduct (start count : Int) : Int :=
  ((List.range' 0 count.toNat).map (fun offset : Nat => start+Int.ofNat offset)).foldr (· * ·) 1

def DigitNumeratorPrefix (upper lower processed : Int) : Int := LucasRangeProduct (upper-lower+1) processed

def DigitDenominatorPrefix (processed : Int) : Int := LucasRangeProduct 1 processed

def DigitBinomialMachineSafe (upper original_lower p : Int) : Prop :=
  let lower := DigitEffectiveLower upper original_lower
  (∀ next : Int,1≤next ∧ next≤lower →
    (0≤Z.modulo (DigitNumeratorPrefix upper lower (next-1)) p*(upper-lower+next) ∧
      Z.modulo (DigitNumeratorPrefix upper lower (next-1)) p*(upper-lower+next)≤2147483647) ∧
    (0≤Z.modulo (DigitDenominatorPrefix (next-1)) p*next ∧ Z.modulo (DigitDenominatorPrefix (next-1)) p*next≤2147483647)) ∧
  (∀ inverse : Int,ModularPower (Z.modulo (DigitDenominatorPrefix lower) p) (p-2) p inverse →
    0≤Z.modulo (DigitNumeratorPrefix upper lower lower) p*inverse ∧ Z.modulo (DigitNumeratorPrefix upper lower lower) p*inverse≤2147483647)

def LucasDigit (value p : Int) (position : Nat) : Int := Z.modulo (Z.div value (Z.pow p (Int.ofNat position))) p

def LucasPrefixProduct (upper lower p : Int) (digits : Nat) : Int :=
  Z.modulo (((List.range' 0 digits).map (fun position => Z.modulo (LucasBinomialCoefficient (LucasDigit upper p position) (LucasDigit lower p position)) p)).foldr (· * ·) 1) p

def LucasMachineSafe (n m p : Int) : Prop :=
  ∀ processed : Nat,
    let upper_digit := LucasDigit (n+m) p processed
    let lower_digit := LucasDigit n p processed
    lower_digit≤upper_digit → DigitBinomialMachineSafe upper_digit lower_digit p ∧
    (0≤LucasPrefixProduct (n+m) n p processed*Z.modulo (LucasBinomialCoefficient upper_digit lower_digit) p ∧
      LucasPrefixProduct (n+m) n p processed*Z.modulo (LucasBinomialCoefficient upper_digit lower_digit) p≤2147483647)

end Algorithms.lucas_theorem.lean
