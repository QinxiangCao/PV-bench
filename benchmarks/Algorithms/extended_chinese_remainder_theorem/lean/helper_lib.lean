import Algorithms.extended_chinese_remainder_theorem.lean.spec_lib

namespace Algorithms.extended_chinese_remainder_theorem.lean

open AUXLib

def CRTPrefixMeaning (residues moduli : List Int) (count answer combined_modulus : Int) : Prop :=
  combined_modulus = CRTLCMPrefix moduli count ∧ CRTAllCongruences residues moduli count answer

def CRTReducedMergeEquation (current_answer current_modulus next_residue next_modulus multiplier : Int) : Prop :=
  let gcd := Z.gcd current_modulus next_modulus
  ∃ adjustment, Z.div current_modulus gcd * multiplier + Z.div next_modulus gcd * adjustment =
    Z.div (next_residue-current_answer) gcd

end Algorithms.extended_chinese_remainder_theorem.lean
