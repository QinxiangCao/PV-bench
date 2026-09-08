import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_goal
import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open lucas_theorem_goal lucas_theorem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_1 : binomial_digit_mod_prime_safety_wit_14_split_goal_1 := by
  unfold binomial_digit_mod_prime_safety_wit_14_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  unfold DigitBinomialMachineSafe DigitEffectiveLower at PreH17
  rw [Int.min_eq_left (by omega)] at PreH17
  have hb := (PreH17.1 i ⟨by omega,by omega⟩).1
  rcases PreH18 with ⟨hn,hd⟩
  rw [←hn] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_2 : binomial_digit_mod_prime_safety_wit_14_split_goal_2 := by
  unfold binomial_digit_mod_prime_safety_wit_14_split_goal_2
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have h : 0≤numerator*(upper_pre-lower_pre+i) := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_binomial_digit_mod_prime_safety_wit_14 : binomial_digit_mod_prime_safety_wit_14 := by
  unfold binomial_digit_mod_prime_safety_wit_14
  right
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_1 : binomial_digit_mod_prime_safety_wit_15_split_goal_1 := by
  unfold binomial_digit_mod_prime_safety_wit_15_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  unfold DigitBinomialMachineSafe DigitEffectiveLower at PreH18
  rw [Int.min_eq_right (by omega)] at PreH18
  have hb := (PreH18.1 i ⟨by omega,by omega⟩).1
  rcases PreH19 with ⟨hn,hd⟩
  rw [←hn] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_2 : binomial_digit_mod_prime_safety_wit_15_split_goal_2 := by
  unfold binomial_digit_mod_prime_safety_wit_15_split_goal_2
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have h : 0≤numerator*(upper_pre-lower+i) := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_binomial_digit_mod_prime_safety_wit_15 : binomial_digit_mod_prime_safety_wit_15 := by
  unfold binomial_digit_mod_prime_safety_wit_15
  right
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_1 : binomial_digit_mod_prime_safety_wit_16_split_goal_1 := by
  unfold binomial_digit_mod_prime_safety_wit_16_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  unfold DigitBinomialMachineSafe DigitEffectiveLower at PreH17
  rw [Int.min_eq_left (by omega)] at PreH17
  have hb := (PreH17.1 i ⟨by omega,by omega⟩).2
  rcases PreH18 with ⟨hn,hd⟩
  rw [←hd] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_2 : binomial_digit_mod_prime_safety_wit_16_split_goal_2 := by
  unfold binomial_digit_mod_prime_safety_wit_16_split_goal_2
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have h : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_binomial_digit_mod_prime_safety_wit_16 : binomial_digit_mod_prime_safety_wit_16 := by
  unfold binomial_digit_mod_prime_safety_wit_16
  right
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_1 : binomial_digit_mod_prime_safety_wit_17_split_goal_1 := by
  unfold binomial_digit_mod_prime_safety_wit_17_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  unfold DigitBinomialMachineSafe DigitEffectiveLower at PreH18
  rw [Int.min_eq_right (by omega)] at PreH18
  have hb := (PreH18.1 i ⟨by omega,by omega⟩).2
  rcases PreH19 with ⟨hn,hd⟩
  rw [←hd] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_2 : binomial_digit_mod_prime_safety_wit_17_split_goal_2 := by
  unfold binomial_digit_mod_prime_safety_wit_17_split_goal_2
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have h : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_binomial_digit_mod_prime_safety_wit_17 : binomial_digit_mod_prime_safety_wit_17 := by
  unfold binomial_digit_mod_prime_safety_wit_17
  right
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_1 : binomial_digit_mod_prime_safety_wit_28_split_goal_1 := by
  unfold binomial_digit_mod_prime_safety_wit_28_split_goal_1
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  subst lower
  unfold DigitBinomialMachineSafe DigitEffectiveLower at PreH19
  rw [Int.min_eq_right (by omega)] at PreH19
  rcases PreH20 with ⟨hn,hd⟩
  simp only [Int.add_sub_cancel] at hn hd
  rw [hd] at PreH3
  have hb := PreH19.2 retval PreH3
  rw [←hn] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_2 : binomial_digit_mod_prime_safety_wit_28_split_goal_2 := by
  unfold binomial_digit_mod_prime_safety_wit_28_split_goal_2
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  dump_pre_spatial
  have h : 0≤numerator*retval := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_binomial_digit_mod_prime_safety_wit_28 : binomial_digit_mod_prime_safety_wit_28 := by
  unfold binomial_digit_mod_prime_safety_wit_28
  right
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_1 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_1 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_2 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_2 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | trivial

theorem proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_1 : binomial_digit_mod_prime_safety_wit_29_split_goal_1 := by
  unfold binomial_digit_mod_prime_safety_wit_29_split_goal_1
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  unfold DigitBinomialMachineSafe DigitEffectiveLower at PreH18
  rw [Int.min_eq_left (by omega)] at PreH18
  rcases PreH19 with ⟨hn,hd⟩
  simp only [Int.add_sub_cancel] at hn hd
  rw [hd] at PreH3
  have hb := PreH18.2 retval PreH3
  rw [←hn] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_2 : binomial_digit_mod_prime_safety_wit_29_split_goal_2 := by
  unfold binomial_digit_mod_prime_safety_wit_29_split_goal_2
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have h : 0≤numerator*retval := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_binomial_digit_mod_prime_safety_wit_29 : binomial_digit_mod_prime_safety_wit_29 := by
  unfold binomial_digit_mod_prime_safety_wit_29
  right
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_1 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_1 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_2 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_2 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 := by
  unfold binomial_digit_mod_prime_entail_wit_1_1_split_goal_1
  intro prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  unfold DigitProductProgress DigitNumeratorPrefix DigitDenominatorPrefix
  simp only [Int.sub_self,lucas_range_product_zero__digit_product_progress]
  constructor <;> symm <;> exact Int.fmod_eq_of_lt (by omega) (by omega)

theorem proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1 := by
  unfold binomial_digit_mod_prime_entail_wit_1_1
  right
  intro prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 := by
  unfold binomial_digit_mod_prime_entail_wit_1_2_split_goal_1
  intro prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  unfold DigitProductProgress DigitNumeratorPrefix DigitDenominatorPrefix
  simp only [Int.sub_self,lucas_range_product_zero__digit_product_progress]
  constructor <;> symm <;> exact Int.fmod_eq_of_lt (by omega) (by omega)

theorem proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2 := by
  unfold binomial_digit_mod_prime_entail_wit_1_2
  right
  intro prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 prime_pre lower_pre upper_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 := by
  unfold binomial_digit_mod_prime_entail_wit_2_1_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hn : 0≤numerator*(upper_pre-lower_pre+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  rw [AUXLib.rem_eq_mod _ _ hn (by omega),AUXLib.rem_eq_mod _ _ hd (by omega)]
  exact digit_product_progress_step__digit_product_progress upper_pre lower_pre prime_pre i numerator denominator (by omega) (by omega) PreH18

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 := by
  unfold binomial_digit_mod_prime_entail_wit_2_1_split_goal_2
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hn : 0≤numerator*(upper_pre-lower_pre+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (denominator*i) prime_pre hd (by omega)).2

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 := by
  unfold binomial_digit_mod_prime_entail_wit_2_1_split_goal_3
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hn : 0≤numerator*(upper_pre-lower_pre+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (denominator*i) prime_pre hd (by omega)).1

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 := by
  unfold binomial_digit_mod_prime_entail_wit_2_1_split_goal_4
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hn : 0≤numerator*(upper_pre-lower_pre+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (numerator*(upper_pre-lower_pre+i)) prime_pre hn (by omega)).2

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 := by
  unfold binomial_digit_mod_prime_entail_wit_2_1_split_goal_5
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hn : 0≤numerator*(upper_pre-lower_pre+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (numerator*(upper_pre-lower_pre+i)) prime_pre hn (by omega)).1

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_1 : binomial_digit_mod_prime_entail_wit_2_1 := by
  unfold binomial_digit_mod_prime_entail_wit_2_1
  right
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 := by
  unfold binomial_digit_mod_prime_entail_wit_2_2_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  have hn : 0≤numerator*(upper_pre-(upper_pre-lower_pre)+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  rw [AUXLib.rem_eq_mod _ _ hn (by omega),AUXLib.rem_eq_mod _ _ hd (by omega)]
  exact digit_product_progress_step__digit_product_progress upper_pre (upper_pre-lower_pre) prime_pre i numerator denominator (by omega) (by omega) PreH19

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 := by
  unfold binomial_digit_mod_prime_entail_wit_2_2_split_goal_2
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  have hn : 0≤numerator*(upper_pre-(upper_pre-lower_pre)+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (denominator*i) prime_pre hd (by omega)).2

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 := by
  unfold binomial_digit_mod_prime_entail_wit_2_2_split_goal_3
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  have hn : 0≤numerator*(upper_pre-(upper_pre-lower_pre)+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (denominator*i) prime_pre hd (by omega)).1

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 := by
  unfold binomial_digit_mod_prime_entail_wit_2_2_split_goal_4
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  have hn : 0≤numerator*(upper_pre-(upper_pre-lower_pre)+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (numerator*(upper_pre-(upper_pre-lower_pre)+i)) prime_pre hn (by omega)).2

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 := by
  unfold binomial_digit_mod_prime_entail_wit_2_2_split_goal_5
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower
  have hn : 0≤numerator*(upper_pre-(upper_pre-lower_pre)+i) := Int.mul_nonneg (by omega) (by omega)
  have hd : 0≤denominator*i := Int.mul_nonneg (by omega) (by omega)
  exact (AUXLib.rem_nonneg_bounds (numerator*(upper_pre-(upper_pre-lower_pre)+i)) prime_pre hn (by omega)).1

theorem proof_of_binomial_digit_mod_prime_entail_wit_2_2 : binomial_digit_mod_prime_entail_wit_2_2 := by
  unfold binomial_digit_mod_prime_entail_wit_2_2
  right
  intro prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 prime_pre lower_pre upper_pre denominator numerator i lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 := by
  unfold binomial_digit_mod_prime_entail_wit_3_1_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [show lower_pre+1=i by omega]
  exact PreH18

theorem proof_of_binomial_digit_mod_prime_entail_wit_3_1 : binomial_digit_mod_prime_entail_wit_3_1 := by
  unfold binomial_digit_mod_prime_entail_wit_3_1
  right
  intro prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 := by
  unfold binomial_digit_mod_prime_entail_wit_3_2_split_goal_1
  intro prime_pre lower_pre upper_pre denominator numerator i lower_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst lower_2
  rw [show upper_pre-lower_pre+1=i by omega]
  exact PreH19

theorem proof_of_binomial_digit_mod_prime_entail_wit_3_2 : binomial_digit_mod_prime_entail_wit_3_2 := by
  unfold binomial_digit_mod_prime_entail_wit_3_2
  right
  intro prime_pre lower_pre upper_pre denominator numerator i lower_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 prime_pre lower_pre upper_pre denominator numerator i lower_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1 : binomial_digit_mod_prime_return_wit_1_split_goal_1 := by
  unfold binomial_digit_mod_prime_return_wit_1_split_goal_1
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  unfold BinomialDigitResidue
  rw [AUXLib.rem_eq_mod _ _ (Int.mul_nonneg (by omega) (by omega)) (by omega)]
  have ht := digit_multiplicative_residue__digit_final_residue upper_pre lower prime_pre numerator denominator retval ⟨by omega,by omega⟩ PreH7 PreH4 PreH20 PreH3
  have hs := lucas_binomial_symmetry_z__digit_final_residue upper_pre lower ⟨by omega,by omega⟩
  rw [show upper_pre-lower=lower_pre by omega] at hs
  rw [hs] at ht
  exact ht

theorem proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_2 : binomial_digit_mod_prime_return_wit_1_split_goal_2 := by
  unfold binomial_digit_mod_prime_return_wit_1_split_goal_2
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact (AUXLib.rem_nonneg_bounds (numerator*retval) prime_pre (Int.mul_nonneg (by omega) (by omega)) (by omega)).2

theorem proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_3 : binomial_digit_mod_prime_return_wit_1_split_goal_3 := by
  unfold binomial_digit_mod_prime_return_wit_1_split_goal_3
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact (AUXLib.rem_nonneg_bounds (numerator*retval) prime_pre (Int.mul_nonneg (by omega) (by omega)) (by omega)).1

theorem proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1 := by
  unfold binomial_digit_mod_prime_return_wit_1
  right
  intro prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_2 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_2 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_3 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
    | exact (proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_3 prime_pre lower_pre upper_pre lower numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
    | trivial

theorem proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_1 : binomial_digit_mod_prime_return_wit_2_split_goal_1 := by
  unfold binomial_digit_mod_prime_return_wit_2_split_goal_1
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  unfold BinomialDigitResidue
  rw [AUXLib.rem_eq_mod _ _ (Int.mul_nonneg (by omega) (by omega)) (by omega)]
  have ht := digit_multiplicative_residue__digit_final_residue upper_pre lower_pre prime_pre numerator denominator retval ⟨by omega,by omega⟩ PreH7 PreH4 PreH19 PreH3
  exact ht

theorem proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_2 : binomial_digit_mod_prime_return_wit_2_split_goal_2 := by
  unfold binomial_digit_mod_prime_return_wit_2_split_goal_2
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (AUXLib.rem_nonneg_bounds (numerator*retval) prime_pre (Int.mul_nonneg (by omega) (by omega)) (by omega)).2

theorem proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_3 : binomial_digit_mod_prime_return_wit_2_split_goal_3 := by
  unfold binomial_digit_mod_prime_return_wit_2_split_goal_3
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact (AUXLib.rem_nonneg_bounds (numerator*retval) prime_pre (Int.mul_nonneg (by omega) (by omega)) (by omega)).1

theorem proof_of_binomial_digit_mod_prime_return_wit_2 : binomial_digit_mod_prime_return_wit_2 := by
  unfold binomial_digit_mod_prime_return_wit_2
  right
  intro prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_1 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_1 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_2 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_2 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | (solve | Goal_apply (proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_3 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_3 prime_pre lower_pre upper_pre numerator denominator retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_lucas_theorem_safety_wit_9_split_goal_1 : lucas_theorem_safety_wit_9_split_goal_1 := by
  unfold lucas_theorem_safety_wit_9_split_goal_1
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH25 with ⟨processed,hu,hl,hr,hres⟩
  have hsafe := PreH11 processed
  rw [AUXLib.rem_eq_mod upper prime_pre (by omega) (by omega)] at PreH17
  rw [AUXLib.rem_eq_mod lower prime_pre (by omega) (by omega)] at PreH18
  have hud : LucasDigit (n_pre+m_pre) prime_pre processed=upper_digit := by unfold LucasDigit; rw [←hu,←PreH17]
  have hld : LucasDigit n_pre prime_pre processed=lower_digit := by unfold LucasDigit; rw [←hl,←PreH18]
  rw [hud,hld] at hsafe
  have hb := (hsafe PreH20).2
  unfold BinomialDigitResidue at PreH3
  rw [←hr,←PreH3] at hb
  dump_pre_spatial
  change _≤2147483647
  exact hb.2

theorem proof_of_lucas_theorem_safety_wit_9_split_goal_2 : lucas_theorem_safety_wit_9_split_goal_2 := by
  unfold lucas_theorem_safety_wit_9_split_goal_2
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  dump_pre_spatial
  have h : 0≤result*retval := Int.mul_nonneg (by omega) (by omega)
  change (-2147483648:Int)≤_
  omega

theorem proof_of_lucas_theorem_safety_wit_9 : lucas_theorem_safety_wit_9 := by
  unfold lucas_theorem_safety_wit_9
  right
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_lucas_theorem_safety_wit_9_split_goal_1 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_safety_wit_9_split_goal_1 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | (solve | Goal_apply (proof_of_lucas_theorem_safety_wit_9_split_goal_2 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_safety_wit_9_split_goal_2 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | trivial

theorem proof_of_lucas_theorem_entail_wit_1_split_goal_1 : lucas_theorem_entail_wit_1_split_goal_1 := by
  unfold lucas_theorem_entail_wit_1_split_goal_1
  intro prime_pre m_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  refine ⟨0,?_,?_,?_,?_⟩
  · simp [Z.div,Z.pow]
  · simp [Z.div,Z.pow]
  · change 1=Z.modulo 1 prime_pre
    symm
    exact Int.fmod_eq_of_lt (by omega) (by omega)
  · simp

theorem proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1 := by
  unfold lucas_theorem_entail_wit_1
  right
  intro prime_pre m_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_1_split_goal_1 prime_pre m_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8))
    | exact (proof_of_lucas_theorem_entail_wit_1_split_goal_1 prime_pre m_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    | trivial

theorem proof_of_lucas_theorem_entail_wit_2_split_goal_1 : lucas_theorem_entail_wit_2_split_goal_1 := by
  unfold lucas_theorem_entail_wit_2_split_goal_1
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  rw [AUXLib.rem_eq_mod upper prime_pre (by omega) (by omega),AUXLib.rem_eq_mod lower prime_pre (by omega) (by omega)] at PreH1 ⊢
  rcases PreH17 with ⟨processed,hu,hl,hr,hres⟩
  have hsafe := PreH10 processed
  unfold LucasDigit at hsafe
  rw [←hu,←hl] at hsafe
  exact (hsafe PreH1).1

theorem proof_of_lucas_theorem_entail_wit_2_split_goal_2 : lucas_theorem_entail_wit_2_split_goal_2 := by
  unfold lucas_theorem_entail_wit_2_split_goal_2
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact (AUXLib.rem_nonneg_bounds upper prime_pre (by omega) (by omega)).2

theorem proof_of_lucas_theorem_entail_wit_2_split_goal_3 : lucas_theorem_entail_wit_2_split_goal_3 := by
  unfold lucas_theorem_entail_wit_2_split_goal_3
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact (AUXLib.rem_nonneg_bounds lower prime_pre (by omega) (by omega)).1

theorem proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2 := by
  unfold lucas_theorem_entail_wit_2
  right
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_2_split_goal_1 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_lucas_theorem_entail_wit_2_split_goal_1 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_2_split_goal_2 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_lucas_theorem_entail_wit_2_split_goal_2 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_2_split_goal_3 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_lucas_theorem_entail_wit_2_split_goal_3 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | trivial

theorem proof_of_lucas_theorem_entail_wit_3_split_goal_1 : lucas_theorem_entail_wit_3_split_goal_1 := by
  unfold lucas_theorem_entail_wit_3_split_goal_1
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  subst upper_digit lower_digit
  exact lucas_progress_advance__lucas_digit_transition (n_pre+m_pre) n_pre prime_pre upper lower result retval (by omega) (by omega) (by omega) PreH13 PreH22 PreH1 PreH10 PreH3 PreH25

theorem proof_of_lucas_theorem_entail_wit_3_split_goal_2 : lucas_theorem_entail_wit_3_split_goal_2 := by
  unfold lucas_theorem_entail_wit_3_split_goal_2
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (AUXLib.rem_nonneg_bounds (result*retval) prime_pre (Int.mul_nonneg PreH22 PreH1) (by omega)).2

theorem proof_of_lucas_theorem_entail_wit_3_split_goal_3 : lucas_theorem_entail_wit_3_split_goal_3 := by
  unfold lucas_theorem_entail_wit_3_split_goal_3
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (AUXLib.rem_nonneg_bounds (result*retval) prime_pre (Int.mul_nonneg PreH22 PreH1) (by omega)).1

theorem proof_of_lucas_theorem_entail_wit_3_split_goal_4 : lucas_theorem_entail_wit_3_split_goal_4 := by
  unfold lucas_theorem_entail_wit_3_split_goal_4
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  apply Z.quot_le_upper_bound upper prime_pre (n_pre+m_pre) (by omega)
  have h := Int.mul_le_mul_of_nonneg_right (by omega : 1≤prime_pre) (by omega : 0≤n_pre+m_pre)
  omega

theorem proof_of_lucas_theorem_entail_wit_3_split_goal_5 : lucas_theorem_entail_wit_3_split_goal_5 := by
  unfold lucas_theorem_entail_wit_3_split_goal_5
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Int.tdiv_le_tdiv (by omega) PreH14

theorem proof_of_lucas_theorem_entail_wit_3_split_goal_6 : lucas_theorem_entail_wit_3_split_goal_6 := by
  unfold lucas_theorem_entail_wit_3_split_goal_6
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact Z.quot_pos lower prime_pre PreH13 (by omega)

theorem proof_of_lucas_theorem_entail_wit_3 : lucas_theorem_entail_wit_3 := by
  unfold lucas_theorem_entail_wit_3
  right
  intro prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_3_split_goal_1 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_entail_wit_3_split_goal_1 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_3_split_goal_2 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_entail_wit_3_split_goal_2 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_3_split_goal_3 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_entail_wit_3_split_goal_3 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_3_split_goal_4 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_entail_wit_3_split_goal_4 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_3_split_goal_5 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_entail_wit_3_split_goal_5 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | (solve | Goal_apply (proof_of_lucas_theorem_entail_wit_3_split_goal_6 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25))
    | exact (proof_of_lucas_theorem_entail_wit_3_split_goal_6 prime_pre m_pre n_pre upper lower upper_digit lower_digit result retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25)
    | trivial

theorem proof_of_lucas_theorem_return_wit_1_split_goal_1 : lucas_theorem_return_wit_1_split_goal_1 := by
  unfold lucas_theorem_return_wit_1_split_goal_1
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hu : upper=0 := by omega
  have hl : lower=0 := by omega
  subst upper lower
  exact lucas_progress_terminal_residue__lucas_terminal_return (n_pre+m_pre) n_pre prime_pre result (by omega) ⟨PreH15,PreH16⟩ PreH17

theorem proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1 := by
  unfold lucas_theorem_return_wit_1
  right
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_lucas_theorem_return_wit_1_split_goal_1 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_lucas_theorem_return_wit_1_split_goal_1 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | trivial

theorem proof_of_lucas_theorem_return_wit_2_split_goal_1 : lucas_theorem_return_wit_2_split_goal_1 := by
  unfold lucas_theorem_return_wit_2_split_goal_1
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  unfold LucasBinomialResidue
  rcases PreH17 with ⟨processed,hu,hl,hr,hres⟩
  rw [hres]
  have hz := lucas_binomial_zero_from_low_digit__lucas_digit_transition upper lower prime_pre (by omega) PreH11 PreH9 PreH1
  unfold Z.modulo at hz ⊢
  rw [Int.mul_fmod,hz,Int.mul_zero,Int.zero_fmod]

theorem proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2 := by
  unfold lucas_theorem_return_wit_2
  right
  intro prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_lucas_theorem_return_wit_2_split_goal_1 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_lucas_theorem_return_wit_2_split_goal_1 prime_pre m_pre n_pre result upper lower PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_proof_manual
