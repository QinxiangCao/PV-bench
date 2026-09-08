import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_goal
import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open concatenating_numbers_dp_goal concatenating_numbers_dp_lib
open scoped SimpleC.SL.SAC CoqZ
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem cell_upper (count width row col : Int) (hw : 0≤width) (hr : row<count) (hc : col<width) :
    row*width+col<count*width := by
  have hm := Int.mul_le_mul_of_nonneg_right (show row+1≤count by omega) hw
  have he : (row+1)*width=row*width+width := by grind
  rw [he] at hm
  omega

private theorem shift_pow (x n : Int) (hn : 0≤n) : Z.shiftl x n=x*Z.pow 2 n := by
  cases n with
  | ofNat n => simp [Z.shiftl,Z.pow,Int.shiftLeft_eq']
  | negSucc n => omega

private theorem pow_nat (n : Int) (hn : 0≤n) : Z.pow 2 n=Int.ofNat (2^n.toNat) := by
  cases n with
  | ofNat n => simp [Z.pow]
  | negSucc n => omega

private theorem shift_small (first count : Int) (hf : 0≤first) (hlt : first<count) (hc : count≤20) :
    signed_last_nbits (Z.shiftl 1 first) 32=Z.shiftl 1 first ∧
    (0≤Z.shiftl 1 first ∧ Z.shiftl 1 first<Z.pow 2 count) := by
  have hc0 : 0≤count := by omega
  have hpow : Z.pow 2 first=Int.ofNat (2^first.toNat) := pow_nat first hf
  have hpowc : Z.pow 2 count=Int.ofNat (2^count.toNat) := pow_nat count hc0
  have hs : Z.shiftl 1 first=Z.pow 2 first := by rw [shift_pow 1 first hf,Int.one_mul]
  have hnat := Nat.pow_lt_pow_of_lt (a:=2) (by decide) (show first.toNat<count.toNat by omega)
  have hmax : (2^first.toNat:Nat)≤2^20 := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : -2147483648≤Z.shiftl 1 first ∧ Z.shiftl 1 first<2147483648 := by
    rw [hs,hpow]
    change (2^first.toNat:Nat)≤1048576 at hmax
    constructor
    · exact Int.le_trans (by decide : (-2147483648:Int)≤0) (Int.natCast_nonneg _)
    · exact Int.lt_of_le_of_lt (Int.ofNat_le.mpr hmax) (by decide)
  refine ⟨signed_last_nbits_eq _ 32 (by decide) hr,?_⟩
  rw [hs,hpow,hpowc]
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hnat⟩

theorem proof_of_compare_concatenated_order_safety_wit_1_split_goal_1 : compare_concatenated_order_safety_wit_1_split_goal_1 := by
  unfold compare_concatenated_order_safety_wit_1_split_goal_1
  intro right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  dump_pre_spatial
  change _≤2147483647
  omega

theorem proof_of_compare_concatenated_order_safety_wit_1_split_goal_2 : compare_concatenated_order_safety_wit_1_split_goal_2 := by
  unfold compare_concatenated_order_safety_wit_1_split_goal_2
  intro right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  dump_pre_spatial
  change (-2147483648:Int)≤_
  omega

theorem proof_of_compare_concatenated_order_safety_wit_1 : compare_concatenated_order_safety_wit_1 := by
  unfold compare_concatenated_order_safety_wit_1
  right
  intro right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_safety_wit_1_split_goal_1 right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_safety_wit_1_split_goal_2 right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 : compare_concatenated_order_entail_wit_1_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact ⟨rfl,rfl,ConcatComparePrefix_zero__compare_bounds rows lens left_pre right_pre⟩

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 : compare_concatenated_order_entail_wit_1_split_goal_2 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_2
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_3 : compare_concatenated_order_entail_wit_1_split_goal_3 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_3
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 : compare_concatenated_order_entail_wit_1_split_goal_4 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_4
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 : compare_concatenated_order_entail_wit_1_split_goal_5 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_5
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 : compare_concatenated_order_entail_wit_1_split_goal_6 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_6
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_7 : compare_concatenated_order_entail_wit_1_split_goal_7 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_7
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_8 : compare_concatenated_order_entail_wit_1_split_goal_8 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_8
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem proof_of_compare_concatenated_order_entail_wit_1 : compare_concatenated_order_entail_wit_1 := by
  unfold compare_concatenated_order_entail_wit_1
  right
  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_3 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_7 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_8 right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 : compare_concatenated_order_entail_wit_3_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_3_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre left_pre position (by omega) (by omega) (by omega)
  omega

theorem proof_of_compare_concatenated_order_entail_wit_3 : compare_concatenated_order_entail_wit_3 := by
  unfold compare_concatenated_order_entail_wit_3
  right
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 : compare_concatenated_order_entail_wit_5_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_5_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre right_pre (position-left_length) (by omega) (by omega) (by omega)
  omega

theorem proof_of_compare_concatenated_order_entail_wit_5 : compare_concatenated_order_entail_wit_5 := by
  unfold compare_concatenated_order_entail_wit_5
  right
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_6_1_split_goal_1 : compare_concatenated_order_entail_wit_6_1_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_6_1_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position PreH34 PreH35 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH36.1 PreH36.2.1).1 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_6_1 : compare_concatenated_order_entail_wit_6_1 := by
  unfold compare_concatenated_order_entail_wit_6_1
  right
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_6_1_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_6_2_split_goal_1 : compare_concatenated_order_entail_wit_6_2_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_6_2_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position PreH32 PreH33 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH34.1 PreH34.2.1).2.1 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_6_2 : compare_concatenated_order_entail_wit_6_2 := by
  unfold compare_concatenated_order_entail_wit_6_2
  right
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_6_2_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 : compare_concatenated_order_entail_wit_8_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_8_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre right_pre position (by omega) (by omega) (by omega)
  omega

theorem proof_of_compare_concatenated_order_entail_wit_8 : compare_concatenated_order_entail_wit_8 := by
  unfold compare_concatenated_order_entail_wit_8
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_10_split_goal_1 : compare_concatenated_order_entail_wit_10_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_10_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre left_pre (position-right_length) (by omega) (by omega) (by omega)
  omega

theorem proof_of_compare_concatenated_order_entail_wit_10 : compare_concatenated_order_entail_wit_10 := by
  unfold compare_concatenated_order_entail_wit_10
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_10_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_11_1_split_goal_1 : compare_concatenated_order_entail_wit_11_1_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_11_1_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position PreH34 PreH35 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH36.1 PreH36.2.1).2.2.1 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_11_1 : compare_concatenated_order_entail_wit_11_1 := by
  unfold compare_concatenated_order_entail_wit_11_1
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_11_1_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_11_2_split_goal_1 : compare_concatenated_order_entail_wit_11_2_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_11_2_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position PreH32 PreH33 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH34.1 PreH34.2.1).2.2.2 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_11_2 : compare_concatenated_order_entail_wit_11_2 := by
  unfold compare_concatenated_order_entail_wit_11_2
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_11_2_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_12_split_goal_1 : compare_concatenated_order_entail_wit_12_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_12_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply concat_compare_prefix_step__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_12 : compare_concatenated_order_entail_wit_12 := by
  unfold compare_concatenated_order_entail_wit_12
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_12_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | trivial

theorem proof_of_compare_concatenated_order_return_wit_1_split_goal_1 : compare_concatenated_order_return_wit_1_split_goal_1 := by
  unfold compare_concatenated_order_return_wit_1_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply concat_compare_outcome_at_end__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_return_wit_1 : compare_concatenated_order_return_wit_1 := by
  unfold compare_concatenated_order_return_wit_1
  right
  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_return_wit_1_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_compare_concatenated_order_return_wit_2_split_goal_1 : compare_concatenated_order_return_wit_2_split_goal_1 := by
  unfold compare_concatenated_order_return_wit_2_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply concat_compare_outcome_at_difference__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position (-1)
  all_goals first | assumption | omega | exact Or.inl ⟨rfl,by omega⟩

theorem proof_of_compare_concatenated_order_return_wit_2 : compare_concatenated_order_return_wit_2 := by
  unfold compare_concatenated_order_return_wit_2
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_return_wit_2_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | trivial

theorem proof_of_compare_concatenated_order_return_wit_3_split_goal_1 : compare_concatenated_order_return_wit_3_split_goal_1 := by
  unfold compare_concatenated_order_return_wit_3_split_goal_1
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply concat_compare_outcome_at_difference__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position 1
  all_goals first | assumption | omega | exact Or.inr ⟨rfl,by omega⟩

theorem proof_of_compare_concatenated_order_return_wit_3 : compare_concatenated_order_return_wit_3 := by
  unfold compare_concatenated_order_return_wit_3
  right
  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_return_wit_3_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_1 : concatenating_numbers_dp_safety_wit_1_split_goal_1 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_1
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hr := signed_Lastnbits_range (1*Z.pow 2 count_pre) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 count_pre) 32 ∧ signed_last_nbits (1*Z.pow 2 count_pre) 32<2147483648 at hr
  dump_pre_spatial
  change signed_last_nbits (1*Z.pow 2 count_pre) 32≤2147483647
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_2 : concatenating_numbers_dp_safety_wit_1_split_goal_2 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_2
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hr := signed_Lastnbits_range (1*Z.pow 2 count_pre) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 count_pre) 32 ∧ signed_last_nbits (1*Z.pow 2 count_pre) 32<2147483648 at hr
  dump_pre_spatial
  change (-2147483648:Int)≤signed_last_nbits (1*Z.pow 2 count_pre) 32
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_3 : concatenating_numbers_dp_safety_wit_1_split_goal_3 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_3
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_4 : concatenating_numbers_dp_safety_wit_1_split_goal_4 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_4
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1 : concatenating_numbers_dp_safety_wit_1 := by
  unfold concatenating_numbers_dp_safety_wit_1
  right
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_1 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_2 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_3 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_4 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | trivial

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_1 : concatenating_numbers_dp_safety_wit_11_split_goal_1 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_1
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hr := signed_Lastnbits_range (bit_value*Z.pow 2 1) 32 (by decide)
  change -2147483648≤signed_last_nbits (bit_value*Z.pow 2 1) 32 ∧ signed_last_nbits (bit_value*Z.pow 2 1) 32<2147483648 at hr
  dump_pre_spatial
  change signed_last_nbits (bit_value*Z.pow 2 1) 32≤2147483647
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_2 : concatenating_numbers_dp_safety_wit_11_split_goal_2 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_2
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hr := signed_Lastnbits_range (bit_value*Z.pow 2 1) 32 (by decide)
  change -2147483648≤signed_last_nbits (bit_value*Z.pow 2 1) 32 ∧ signed_last_nbits (bit_value*Z.pow 2 1) 32<2147483648 at hr
  dump_pre_spatial
  change (-2147483648:Int)≤signed_last_nbits (bit_value*Z.pow 2 1) 32
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_3 : concatenating_numbers_dp_safety_wit_11_split_goal_3 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_3
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_4 : concatenating_numbers_dp_safety_wit_11_split_goal_4 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_4
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11 : concatenating_numbers_dp_safety_wit_11 := by
  unfold concatenating_numbers_dp_safety_wit_11
  right
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_1 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_2 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_3 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_4 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | trivial

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_1 : concatenating_numbers_dp_safety_wit_28_split_goal_1 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_1
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hr := signed_Lastnbits_range (1*Z.pow 2 first) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 first) 32 ∧ signed_last_nbits (1*Z.pow 2 first) 32<2147483648 at hr
  dump_pre_spatial
  change signed_last_nbits (1*Z.pow 2 first) 32≤2147483647
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2 : concatenating_numbers_dp_safety_wit_28_split_goal_2 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_2
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hr := signed_Lastnbits_range (1*Z.pow 2 first) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 first) 32 ∧ signed_last_nbits (1*Z.pow 2 first) 32<2147483648 at hr
  dump_pre_spatial
  change (-2147483648:Int)≤signed_last_nbits (1*Z.pow 2 first) 32
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_3 : concatenating_numbers_dp_safety_wit_28_split_goal_3 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_3
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_4 : concatenating_numbers_dp_safety_wit_28_split_goal_4 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_4
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28 : concatenating_numbers_dp_safety_wit_28 := by
  unfold concatenating_numbers_dp_safety_wit_28
  right
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_1 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_3 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_4 result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_1 : concatenating_numbers_dp_entail_wit_1 := by
  unfold concatenating_numbers_dp_entail_wit_1
  left
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hs : signed_last_nbits (Z.shiftl 1 count_pre) 32=Z.shiftl 1 count_pre :=
    signed_last_nbits_eq _ 32 (by decide) (by change -2147483648≤_ ∧ _<2147483648;omega)
  rw [hs]
  sep_apply (naive_C_Rules.IntArray.seg_single best_first_pre 0 (-1 : Int))
  simp only [Int.zero_add]
  Exists ([-1] : List Int)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact dp_table_prefix_singleton__dp_initialization rows lens count_pre (by omega)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 : concatenating_numbers_dp_entail_wit_2_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_2_split_goal_1
  intro number_width_pre count_pre flat lens rows choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  refine ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,rfl,?_⟩
  intro lower hl
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_2 : concatenating_numbers_dp_entail_wit_2 := by
  unfold concatenating_numbers_dp_entail_wit_2
  right
  intro number_width_pre count_pre flat lens rows choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 number_width_pre count_pre flat lens rows choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1 : concatenating_numbers_dp_entail_wit_3_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_1
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  rw [he]
  exact ⟨PreH19.1,⟨by omega,by omega⟩,ha.2.2.1,ha.2.2.2.2.2⟩

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 : concatenating_numbers_dp_entail_wit_3_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_2
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  rw [he]
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 : concatenating_numbers_dp_entail_wit_3_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_3
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  rw [he]
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4 : concatenating_numbers_dp_entail_wit_3_split_goal_4 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_4
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3 : concatenating_numbers_dp_entail_wit_3 := by
  unfold concatenating_numbers_dp_entail_wit_3
  right
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 : concatenating_numbers_dp_entail_wit_4_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_1
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  exact ⟨PreH19,PreH1,⟨by omega,ha.1⟩,ha.2.1,rfl,ha.2.2.2.1⟩

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 : concatenating_numbers_dp_entail_wit_4_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_2
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 : concatenating_numbers_dp_entail_wit_4_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_3
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 : concatenating_numbers_dp_entail_wit_4_split_goal_4 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_4
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 : concatenating_numbers_dp_entail_wit_4_split_goal_5 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_5
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4 : concatenating_numbers_dp_entail_wit_4 := by
  unfold concatenating_numbers_dp_entail_wit_4
  right
  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_5 : concatenating_numbers_dp_entail_wit_5 := by
  unfold concatenating_numbers_dp_entail_wit_5
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices state_count mask bit bit_value rest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hz := PreH19.2.2.1
  by_cases he : rest=0
  · Left
    Exists choices
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first
      | (simpa only [he,Int.sub_zero] using hz)
      | (simp only [Int.sub_zero])
      | assumption
      | omega
      | rfl
      | trivial
  · have hb := PreH19.2.2.2 rest ⟨by omega,by omega⟩
    have hi := hb.1
    simp only [Int.sub_zero]
    Right
    Exists choices
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first
      | exact hb
      | assumption
      | omega
      | rfl
      | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 : concatenating_numbers_dp_entail_wit_6_1_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_1_split_goal_1
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply dp_table_prefix_extend__dp_table_transition rows lens count_pre mask choices_2 _ PreH21 (by omega)
  exact best_index_singleton__dp_table_transition rows lens count_pre mask bit bit_value rest PreH22 PreH17

theorem proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 : concatenating_numbers_dp_entail_wit_6_1_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_1_split_goal_2
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_1 : concatenating_numbers_dp_entail_wit_6_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_1
  right
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 : concatenating_numbers_dp_entail_wit_6_2_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_2_split_goal_1
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply dp_table_prefix_extend__dp_table_transition rows lens count_pre mask choices_2 _ PreH25 (by omega)
  exact best_index_choose_bit__dp_table_transition rows lens count_pre number_width_pre mask bit bit_value rest previous_best retval PreH23 PreH26 PreH22 PreH1 PreH2

theorem proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 : concatenating_numbers_dp_entail_wit_6_2_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_2_split_goal_2
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_2 : concatenating_numbers_dp_entail_wit_6_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_2
  right
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 : concatenating_numbers_dp_entail_wit_6_3_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_3_split_goal_1
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply dp_table_prefix_extend__dp_table_transition rows lens count_pre mask choices_2 _ PreH25 (by omega)
  exact best_index_keep_previous__dp_table_transition rows lens count_pre mask bit bit_value rest previous_best retval PreH26 PreH22 PreH1 PreH2

theorem proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 : concatenating_numbers_dp_entail_wit_6_3_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_3_split_goal_2
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_3 : concatenating_numbers_dp_entail_wit_6_3 := by
  unfold concatenating_numbers_dp_entail_wit_6_3
  right
  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_8 : concatenating_numbers_dp_entail_wit_8 := by
  unfold concatenating_numbers_dp_entail_wit_8
  right
  intro best_first_pre number_width_pre count_pre flat lens rows choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have he : mask=state_count := by omega
  subst mask
  have hg := greedy_output_full_mask__output_initialization rows lens count_pre PreH11.1 (by omega)
  Exists choices_2
  split_pure_spatial
  · rw [he]
    sep_apply (naive_C_Rules.IntArray.seg_to_full best_first_pre 0 state_count choices_2)
    simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (rw [←he]; exact PreH14)
    | (rw [PreH2]; exact hg)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_1 : concatenating_numbers_dp_entail_wit_9_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_9_split_goal_1
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := PreH17.2.2.2 mask ⟨by omega,by omega⟩
  exact hb

theorem proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_2 : concatenating_numbers_dp_entail_wit_9_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_9_split_goal_2
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := PreH17.2.2.2 mask ⟨by omega,by omega⟩
  rw [PreH11]
  exact greedy_output_remaining_length__output_initialization rows lens count_pre number_width_pre mask output_2 (Znth mask choices 0) PreH14 PreH18 hb.1 hb.2.1

theorem proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_3 : concatenating_numbers_dp_entail_wit_9_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_9_split_goal_3
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := PreH17.2.2.2 mask ⟨by omega,by omega⟩
  have hr := PreH14.2.2 (Znth mask choices 0) hb.1
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_4 : concatenating_numbers_dp_entail_wit_9_split_goal_4 := by
  unfold concatenating_numbers_dp_entail_wit_9_split_goal_4
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := PreH17.2.2.2 mask ⟨by omega,by omega⟩
  have hr := PreH14.2.2 (Znth mask choices 0) hb.1
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_5 : concatenating_numbers_dp_entail_wit_9_split_goal_5 := by
  unfold concatenating_numbers_dp_entail_wit_9_split_goal_5
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := PreH17.2.2.2 mask ⟨by omega,by omega⟩
  exact hb.1.2

theorem proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_6 : concatenating_numbers_dp_entail_wit_9_split_goal_6 := by
  unfold concatenating_numbers_dp_entail_wit_9_split_goal_6
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := PreH17.2.2.2 mask ⟨by omega,by omega⟩
  exact hb.1.1

theorem proof_of_concatenating_numbers_dp_entail_wit_9 : concatenating_numbers_dp_entail_wit_9 := by
  unfold concatenating_numbers_dp_entail_wit_9
  right
  intro number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_1 number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_2 number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_3 number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_4 number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_5 number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_9_split_goal_6 number_width_pre count_pre flat lens rows choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_10 : concatenating_numbers_dp_entail_wit_10 := by
  unfold concatenating_numbers_dp_entail_wit_10
  left
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices_2 output_2 state_count mask first result_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  Exists output_2 output_2 choices_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | simp [AppendRowPrefix,sublist])
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_11_split_goal_1 : concatenating_numbers_dp_entail_wit_11_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_11_split_goal_1
  intro number_width_pre count_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  exact cell_upper count_pre number_width_pre first position (by omega) (by omega) (by omega)

theorem proof_of_concatenating_numbers_dp_entail_wit_11 : concatenating_numbers_dp_entail_wit_11 := by
  unfold concatenating_numbers_dp_entail_wit_11
  right
  intro number_width_pre count_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_11_split_goal_1 number_width_pre count_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41))
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_13 : concatenating_numbers_dp_entail_wit_13 := by
  unfold concatenating_numbers_dp_entail_wit_13
  left
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows prior_2 output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  have hp : AppendRowPrefix rows lens prior_2 first (position+1) (output_2++[Znth (first*number_width_pre+position) flat 0]) := by
    apply append_row_prefix_step__output_row_copy flat rows lens count_pre number_width_pre prior_2 output_2 first position
    all_goals first | assumption | omega
  have hl : result_length+1=Zlength (output_2++[Znth (first*number_width_pre+position) flat 0]) := by
    simp only [Zlength_app,Zlength_cons,Zlength_nil]
    omega
  Exists prior_2 (output_2++[Znth (first*number_width_pre+position) flat 0]) choices_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hp
    | exact hl
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_1 : concatenating_numbers_dp_entail_wit_14_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_14_split_goal_1
  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := shift_small first count_pre PreH13 PreH14 PreH4
  rw [hs.1]
  exact greedy_output_consume_best__output_finalization rows lens count_pre number_width_pre mask first prior output_2 position PreH22 PreH25 PreH26 PreH27 PreH1 PreH16

theorem proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_2 : concatenating_numbers_dp_entail_wit_14_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_14_split_goal_2
  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := shift_small first count_pre PreH13 PreH14 PreH4
  rw [hs.1]
  have he : Z.shiftl 1 count_pre=Z.pow 2 count_pre := by rw [shift_pow 1 count_pre (by omega),Int.one_mul]
  have hm : 0≤mask ∧ mask<Z.pow 2 count_pre := by rw [←he];omega
  have hx := lxor_lt_pow2__output_finalization mask (Z.shiftl 1 first) count_pre hm hs.2 (by omega)
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_3 : concatenating_numbers_dp_entail_wit_14_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_14_split_goal_3
  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := shift_small first count_pre PreH13 PreH14 PreH4
  rw [hs.1]
  have he : Z.shiftl 1 count_pre=Z.pow 2 count_pre := by rw [shift_pow 1 count_pre (by omega),Int.one_mul]
  have hm : 0≤mask ∧ mask<Z.pow 2 count_pre := by rw [←he];omega
  have hx := lxor_lt_pow2__output_finalization mask (Z.shiftl 1 first) count_pre hm hs.2 (by omega)
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_14 : concatenating_numbers_dp_entail_wit_14 := by
  unfold concatenating_numbers_dp_entail_wit_14
  right
  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_1 number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_2 number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_14_split_goal_3 number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | trivial

theorem proof_of_concatenating_numbers_dp_return_wit_1 : concatenating_numbers_dp_return_wit_1 := by
  unfold concatenating_numbers_dp_return_wit_1
  left
  intro result_pre best_first_pre lengths_pre number_width_pre count_pre numbers_pre flat lens rows choices_2 output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hg : GreedyOutputPrefix rows lens count_pre 0 output_2 := by rw [←PreH1];exact PreH18
  have hf := greedy_output_empty_mask__output_finalization rows lens count_pre number_width_pre output_2 PreH14 hg
  have he : result_length=sum lens := by have := hf.2;omega
  Exists output_2 choices_2
  split_pure_spatial
  · rw [he]
    sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (naive_C_Rules.IntArray.undef_seg_empty result_pre (sum lens))).1)
    sep_apply (naive_C_Rules.IntArray.seg_to_full result_pre 0 (sum lens) output_2)
    simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
    rw [←PreH2]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hf.1
    | exact hf.2
    | (rw [←PreH2];exact PreH17)
    | assumption
    | omega
    | rfl
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_proof_manual
