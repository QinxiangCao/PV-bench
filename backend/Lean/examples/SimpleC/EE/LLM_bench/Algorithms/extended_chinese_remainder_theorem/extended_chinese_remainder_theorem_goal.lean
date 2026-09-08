import SimpleC.SL.SeparationLogic

import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance extended_chinese_remainder_theorem_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def extended_chinese_remainder_theorem_safety_wit_1 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_2 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((( &( "lcm" ) )) # Int |->_)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((( &( "answer" ) )) # Int |-> ((Znth (0 : Int) residue_values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_3 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "lcm" ) )) # Int |-> ((Znth (0 : Int) modulus_values (0 : Int))))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((( &( "answer" ) )) # Int |-> ((Znth (0 : Int) residue_values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_4 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i modulus_values (0 : Int)) ≠ (INT_MIN)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_5 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "reduced_modulus" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |-> (x_callee_v))
  ** ((( &( "y" ) )) # Int |-> (y_callee_v))
  ** ((( &( "gcd" ) )) # Int |-> (retval))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth i modulus_values (0 : Int)) ≠ (INT_MIN)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_6 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((((Znth (i) (residue_values) ((0 : Int))) - answer) ≠ (INT_MIN)) ∨ (gcd ≠ (-1))) ” &&
  “ (gcd ≠ (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_7 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth (i) (residue_values) ((0 : Int))) - answer) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i) (residue_values) ((0 : Int))) - answer)) ”
) \/
(
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth (i) (residue_values) ((0 : Int))) - answer) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i) (residue_values) ((0 : Int))) - answer)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((Znth (i) (residue_values) ((0 : Int))) - answer) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((INT_MIN) <= ((Znth (i) (residue_values) ((0 : Int))) - answer)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_8 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= answer)) (PreH9 : (answer < lcm)) (PreH10 : ((0 : Int) < lcm)) (PreH11 : (lcm <= INT_MAX)) (PreH12 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH13 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH14 : ((0 : Int) < gcd)) (PreH15 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH16 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH17 : ((0 : Int) < reduced_modulus)) (PreH18 : ((reduced_modulus * 2) <= INT_MAX)) (PreH19 : (((0 : Int) - reduced_modulus) < x)) (PreH20 : (x < reduced_modulus)) (PreH21 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH22 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (intArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_9 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (intArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (retval))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((retval + reduced_modulus) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval + reduced_modulus)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_10 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((answer + (x * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + (x * lcm))) ”
) \/
(
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((answer + (x * lcm)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (answer + (x * lcm))) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((answer + (x * lcm)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((INT_MIN) <= (answer + (x * lcm))) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_11 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((x * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x * lcm)) ”
) \/
(
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((x * lcm) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x * lcm)) ”
)

noncomputable def extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((x * lcm) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((INT_MIN) <= (x * lcm)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_12 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + (x * lcm))))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
|--
  “ ((lcm * reduced_modulus) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lcm * reduced_modulus)) ”

noncomputable def extended_chinese_remainder_theorem_safety_wit_13 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> ((answer + (x * lcm))))
  ** ((( &( "lcm" ) )) # Int |-> ((lcm * reduced_modulus)))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def extended_chinese_remainder_theorem_entail_wit_1 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  (1 <= n_pre)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) residue_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) residue_values (0 : Int)) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((0 : Int) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth (0 : Int) residue_values (0 : Int)) (Znth (0 : Int) modulus_values (0 : Int))) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values 1 (Znth (0 : Int) residue_values (0 : Int)) (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ ((0 : Int) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) residue_values (0 : Int)) < (Znth (0 : Int) modulus_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) residue_values (0 : Int))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  (CRTPrefixMeaning residue_values modulus_values 1 (Znth (0 : Int) residue_values (0 : Int)) (Znth (0 : Int) modulus_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((Znth (0 : Int) modulus_values (0 : Int)) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((0 : Int) < (Znth (0 : Int) modulus_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((Znth (0 : Int) residue_values (0 : Int)) < (Znth (0 : Int) modulus_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  ((0 : Int) <= (Znth (0 : Int) residue_values (0 : Int)))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ” &&
  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (((lcm * x_callee_v) + ((Znth (i) (modulus_values) ((0 : Int))) * y_callee_v)) = retval) ” &&
  “ ((Z.quot (Znth i modulus_values (0 : Int)) retval) = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) retval)) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_callee_v) ” &&
  “ (x_callee_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval)) ” &&
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval) <= INT_MAX) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval)) ” &&
  “ (x_callee_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_callee_v) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((lcm * x_callee_v) + ((Znth (i) (modulus_values) ((0 : Int))) * y_callee_v)) = retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (x_callee_v < (Z.quot (Znth i modulus_values (0 : Int)) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_callee_v)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (((lcm * x_callee_v) + ((Znth (i) (modulus_values) ((0 : Int))) * y_callee_v)) = retval)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ” &&
  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ” &&
  “ ((0 : Int) < retval) ” &&
  “ (((lcm * x_callee_v) + ((Znth (i) (modulus_values) ((0 : Int))) * y_callee_v)) = retval) ” &&
  “ ((Z.quot (Znth i modulus_values (0 : Int)) retval) = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) retval)) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < x_callee_v) ” &&
  “ (x_callee_v < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval)) ” &&
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval) <= INT_MAX) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval) <= INT_MAX) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval)) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int)) ” &&
  “ (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX) ” &&
  “ ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ (((lcm * (0 : Int)) + ((Znth (i) (modulus_values) ((0 : Int))) * y_callee_v)) = retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (((0 : Int) - (Z.quot (Znth i modulus_values (0 : Int)) retval)) < (0 : Int))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (((Z.quot (Znth i modulus_values (0 : Int)) retval) * 2) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  ((0 : Int) < (Z.quot (Znth i modulus_values (0 : Int)) retval))

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (((lcm * (0 : Int)) + ((Znth (i) (modulus_values) ((0 : Int))) * y_callee_v)) = retval)

noncomputable def extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (retval = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_1 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (intArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ” &&
  “ (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ” &&
  “ ((0 : Int) < gcd) ” &&
  “ (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd)) ” &&
  “ ((0 : Int) < reduced_modulus) ” &&
  “ (reduced_modulus <= INT_MAX) ” &&
  “ ((0 : Int) <= (retval + reduced_modulus)) ” &&
  “ ((retval + reduced_modulus) < reduced_modulus) ” &&
  “ ((0 : Int) < (lcm * reduced_modulus)) ” &&
  “ ((lcm * reduced_modulus) <= INT_MAX) ” &&
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval + reduced_modulus)) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval + reduced_modulus)) ” &&
  “ ((lcm * reduced_modulus) <= INT_MAX) ” &&
  “ ((0 : Int) <= (retval + reduced_modulus)) ” &&
  “ ((replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)) = residue_values) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) (retval + reduced_modulus))

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((lcm * reduced_modulus) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((0 : Int) <= (retval + reduced_modulus))

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval < (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)) = residue_values)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_2 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (intArray.full residues_pre n_pre (replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ” &&
  “ (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ” &&
  “ ((0 : Int) < gcd) ” &&
  “ (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd)) ” &&
  “ ((0 : Int) < reduced_modulus) ” &&
  “ (reduced_modulus <= INT_MAX) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < reduced_modulus) ” &&
  “ ((0 : Int) < (lcm * reduced_modulus)) ” &&
  “ ((lcm * reduced_modulus) <= INT_MAX) ” &&
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  TT && emp 
|--
  “ (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval) ” &&
  “ ((lcm * reduced_modulus) <= INT_MAX) ” &&
  “ (retval < reduced_modulus) ” &&
  “ ((replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)) = residue_values) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) retval)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((lcm * reduced_modulus) <= INT_MAX)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (retval < reduced_modulus)

noncomputable def extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (ModularMul x (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) reduced_modulus retval)) (PreH3 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH5 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (1 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= answer)) (PreH10 : (answer < lcm)) (PreH11 : ((0 : Int) < lcm)) (PreH12 : (lcm <= INT_MAX)) (PreH13 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH14 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH15 : ((0 : Int) < gcd)) (PreH16 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH17 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH18 : ((0 : Int) < reduced_modulus)) (PreH19 : ((reduced_modulus * 2) <= INT_MAX)) (PreH20 : (((0 : Int) - reduced_modulus) < x)) (PreH21 : (x < reduced_modulus)) (PreH22 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH23 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((replace_Znth (i) ((Znth (i) (residue_values) ((0 : Int)))) (residue_values)) = residue_values)

noncomputable def extended_chinese_remainder_theorem_entail_wit_5 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (answer + (x * lcm))) ” &&
  “ ((answer + (x * lcm)) < (lcm * reduced_modulus)) ” &&
  “ ((0 : Int) < (lcm * reduced_modulus)) ” &&
  “ ((lcm * reduced_modulus) <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (x * lcm)) (lcm * reduced_modulus)) ”
  &&  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  TT && emp 
|--
  “ (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (x * lcm)) (lcm * reduced_modulus)) ” &&
  “ ((answer + (x * lcm)) < (lcm * reduced_modulus)) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  (CRTPrefixMeaning residue_values modulus_values (i + 1) (answer + (x * lcm)) (lcm * reduced_modulus))

noncomputable def extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (reduced_modulus : Int) (x : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= answer)) (PreH7 : (answer < lcm)) (PreH8 : ((0 : Int) < lcm)) (PreH9 : (lcm <= INT_MAX)) (PreH10 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH11 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH12 : ((0 : Int) < gcd)) (PreH13 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH14 : ((0 : Int) < reduced_modulus)) (PreH15 : (reduced_modulus <= INT_MAX)) (PreH16 : ((0 : Int) <= x)) (PreH17 : (x < reduced_modulus)) (PreH18 : ((0 : Int) < (lcm * reduced_modulus))) (PreH19 : ((lcm * reduced_modulus) <= INT_MAX)) (PreH20 : (CRTReducedMergeEquation answer lcm (Znth (i) (residue_values) ((0 : Int))) (Znth (i) (modulus_values) ((0 : Int))) x)) ,
  ((answer + (x * lcm)) < (lcm * reduced_modulus))

noncomputable def extended_chinese_remainder_theorem_return_wit_1 : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |-> (lcm))
|--
  EX combined_modulus_pre_v : Int,
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer combined_modulus_pre_v) ”
  &&  ((combined_modulus_pre) # Int |-> (combined_modulus_pre_v))
  ** (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
) \/
(
forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  TT && emp 
|--
  “ (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm) ”
  &&  emp
)

noncomputable def extended_chinese_remainder_theorem_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (ExtendedCRTSystemResult residue_values modulus_values n_pre answer lcm)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_1 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ”
  &&  (((residues_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) residue_values (0 : Int))))
  ** (intArray.missing_i residues_pre (0 : Int) (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_2 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ”
  &&  (((moduli_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre (0 : Int) (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_3 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full residues_pre n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (i < n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_pure : Prop :=
  (
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ”
) \/
(
forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH11 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= answer)) (PreH15 : (answer < lcm)) (PreH16 : ((0 : Int) < lcm)) (PreH17 : (lcm <= INT_MAX)) (PreH18 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ” &&
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ”
)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH11 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= answer)) (PreH15 : (answer < lcm)) (PreH16 : ((0 : Int) < lcm)) (PreH17 : (lcm <= INT_MAX)) (PreH18 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (answer <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (lcm >= INT_MIN)) (PreH5 : (answer >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i < n_pre)) (PreH9 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH11 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((0 : Int) <= answer)) (PreH15 : (answer < lcm)) (PreH16 : ((0 : Int) < lcm)) (PreH17 : (lcm <= INT_MAX)) (PreH18 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** ((( &( "gcd" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4_aux : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH4 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ ((Znth i modulus_values (0 : Int)) <= INT_MAX) ” &&
  “ ((0 : Int) < (Znth i modulus_values (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_4 : Prop := extended_chinese_remainder_theorem_partial_solve_wit_4_pure -> extended_chinese_remainder_theorem_partial_solve_wit_4_aux

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_5 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int))) (PreH6 : (i < n_pre)) (PreH7 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH8 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer < lcm)) (PreH14 : ((0 : Int) < lcm)) (PreH15 : (lcm <= INT_MAX)) (PreH16 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval) ” &&
  “ ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_6 : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (lcm : Int) (answer : Int) (i : Int) (y_callee_v : Int) (x_callee_v : Int) (retval : Int) (PreH1 : ((0 : Int) < retval)) (PreH2 : (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int)))))) (PreH3 : (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval)) (PreH4 : ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval))) (PreH5 : ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int))) (PreH6 : (x_callee_v = (0 : Int))) (PreH7 : (i < n_pre)) (PreH8 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH9 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH10 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer < lcm)) (PreH15 : ((0 : Int) < lcm)) (PreH16 : (lcm <= INT_MAX)) (PreH17 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) ,
  (intArray.full moduli_pre n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ ((0 : Int) < retval) ” &&
  “ (retval = (Zgcd (lcm) ((Znth i modulus_values (0 : Int))))) ” &&
  “ (((lcm * x_callee_v) + ((Znth i modulus_values (0 : Int)) * y_callee_v)) = retval) ” &&
  “ ((Zabs (x_callee_v)) <= (Z.quot (Znth i modulus_values (0 : Int)) retval)) ” &&
  “ ((Z.rem lcm (Znth i modulus_values (0 : Int))) = (0 : Int)) ” &&
  “ (x_callee_v = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int |-> ((Znth i modulus_values (0 : Int))))
  ** (intArray.missing_i moduli_pre i (0 : Int) n_pre modulus_values)
  ** (intArray.full residues_pre n_pre residue_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_7_pure : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "residues" ) )) # Ptr |-> (residues_pre))
  ** ((( &( "moduli" ) )) # Ptr |-> (moduli_pre))
  ** ((( &( "combined_modulus" ) )) # Ptr |-> (combined_modulus_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** ((( &( "lcm" ) )) # Int |-> (lcm))
  ** ((( &( "gcd" ) )) # Int |-> (gcd))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "reduced_modulus" ) )) # Int |-> (reduced_modulus))
  ** (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - reduced_modulus) < x) ” &&
  “ (x < reduced_modulus) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd)) ” &&
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX) ” &&
  “ ((0 : Int) < reduced_modulus) ” &&
  “ ((reduced_modulus * 2) <= INT_MAX) ”

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_7_aux : Prop :=
  forall (combined_modulus_pre : Int) (moduli_pre : Int) (residues_pre : Int) (n_pre : Int) (modulus_values : (List Int)) (residue_values : (List Int)) (i : Int) (answer : Int) (lcm : Int) (gcd : Int) (x : Int) (y : Int) (reduced_modulus : Int) (PreH1 : (ExtendedCRTInputs residue_values modulus_values n_pre)) (PreH2 : (ExtendedCRTSystemCompatible residue_values modulus_values n_pre)) (PreH3 : (ExtendedCRTIntSafe modulus_values n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= answer)) (PreH8 : (answer < lcm)) (PreH9 : ((0 : Int) < lcm)) (PreH10 : (lcm <= INT_MAX)) (PreH11 : (CRTPrefixMeaning residue_values modulus_values i answer lcm)) (PreH12 : (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int))))))) (PreH13 : ((0 : Int) < gcd)) (PreH14 : (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd)) (PreH15 : (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd))) (PreH16 : ((0 : Int) < reduced_modulus)) (PreH17 : ((reduced_modulus * 2) <= INT_MAX)) (PreH18 : (((0 : Int) - reduced_modulus) < x)) (PreH19 : (x < reduced_modulus)) (PreH20 : (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd))) (PreH21 : ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX)) ,
  (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)
|--
  “ (((0 : Int) - reduced_modulus) < x) ” &&
  “ (x < reduced_modulus) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd)) ” &&
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX) ” &&
  “ ((0 : Int) < reduced_modulus) ” &&
  “ ((reduced_modulus * 2) <= INT_MAX) ” &&
  “ (ExtendedCRTInputs residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTSystemCompatible residue_values modulus_values n_pre) ” &&
  “ (ExtendedCRTIntSafe modulus_values n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer < lcm) ” &&
  “ ((0 : Int) < lcm) ” &&
  “ (lcm <= INT_MAX) ” &&
  “ (CRTPrefixMeaning residue_values modulus_values i answer lcm) ” &&
  “ (gcd = (Zgcd (lcm) ((Znth (i) (modulus_values) ((0 : Int)))))) ” &&
  “ ((0 : Int) < gcd) ” &&
  “ (((lcm * x) + ((Znth (i) (modulus_values) ((0 : Int))) * y)) = gcd) ” &&
  “ (reduced_modulus = (Z.quot (Znth (i) (modulus_values) ((0 : Int))) gcd)) ” &&
  “ ((0 : Int) < reduced_modulus) ” &&
  “ ((reduced_modulus * 2) <= INT_MAX) ” &&
  “ (((0 : Int) - reduced_modulus) < x) ” &&
  “ (x < reduced_modulus) ” &&
  “ (INT_MIN < (Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd)) ” &&
  “ ((Z.quot ((Znth (i) (residue_values) ((0 : Int))) - answer) gcd) <= INT_MAX) ”
  &&  (((residues_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i) (residue_values) ((0 : Int)))))
  ** (intArray.missing_i residues_pre i (0 : Int) n_pre residue_values)
  ** (intArray.full moduli_pre n_pre modulus_values)
  ** ((combined_modulus_pre) # Int |->_)

noncomputable def extended_chinese_remainder_theorem_partial_solve_wit_7 : Prop := extended_chinese_remainder_theorem_partial_solve_wit_7_pure -> extended_chinese_remainder_theorem_partial_solve_wit_7_aux


structure VC_Correct : Type where
  proof_of_extended_chinese_remainder_theorem_safety_wit_1 : extended_chinese_remainder_theorem_safety_wit_1
  proof_of_extended_chinese_remainder_theorem_safety_wit_2 : extended_chinese_remainder_theorem_safety_wit_2
  proof_of_extended_chinese_remainder_theorem_safety_wit_3 : extended_chinese_remainder_theorem_safety_wit_3
  proof_of_extended_chinese_remainder_theorem_safety_wit_4 : extended_chinese_remainder_theorem_safety_wit_4
  proof_of_extended_chinese_remainder_theorem_safety_wit_5 : extended_chinese_remainder_theorem_safety_wit_5
  proof_of_extended_chinese_remainder_theorem_safety_wit_6 : extended_chinese_remainder_theorem_safety_wit_6
  proof_of_extended_chinese_remainder_theorem_safety_wit_8 : extended_chinese_remainder_theorem_safety_wit_8
  proof_of_extended_chinese_remainder_theorem_safety_wit_9 : extended_chinese_remainder_theorem_safety_wit_9
  proof_of_extended_chinese_remainder_theorem_safety_wit_12 : extended_chinese_remainder_theorem_safety_wit_12
  proof_of_extended_chinese_remainder_theorem_safety_wit_13 : extended_chinese_remainder_theorem_safety_wit_13
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_1 : extended_chinese_remainder_theorem_partial_solve_wit_1
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_2 : extended_chinese_remainder_theorem_partial_solve_wit_2
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_3 : extended_chinese_remainder_theorem_partial_solve_wit_3
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4 : extended_chinese_remainder_theorem_partial_solve_wit_4
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_5 : extended_chinese_remainder_theorem_partial_solve_wit_5
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_6 : extended_chinese_remainder_theorem_partial_solve_wit_6
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_7_pure : extended_chinese_remainder_theorem_partial_solve_wit_7_pure
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_7 : extended_chinese_remainder_theorem_partial_solve_wit_7
  proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7
  proof_of_extended_chinese_remainder_theorem_safety_wit_10 : extended_chinese_remainder_theorem_safety_wit_10
  proof_of_extended_chinese_remainder_theorem_safety_wit_11 : extended_chinese_remainder_theorem_safety_wit_11
  proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1
  proof_of_extended_chinese_remainder_theorem_entail_wit_2 : extended_chinese_remainder_theorem_entail_wit_2
  proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1
  proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2
  proof_of_extended_chinese_remainder_theorem_entail_wit_4_1 : extended_chinese_remainder_theorem_entail_wit_4_1
  proof_of_extended_chinese_remainder_theorem_entail_wit_4_2 : extended_chinese_remainder_theorem_entail_wit_4_2
  proof_of_extended_chinese_remainder_theorem_entail_wit_5 : extended_chinese_remainder_theorem_entail_wit_5
  proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1
  proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure

end SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_goal
