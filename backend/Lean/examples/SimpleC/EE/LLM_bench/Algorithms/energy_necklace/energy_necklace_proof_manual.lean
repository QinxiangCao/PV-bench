import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal
import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open energy_necklace_goal energy_necklace_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem app_nth (l : List Int) (x i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    Znth i (l++[x]) 0 = Znth i l 0 := ListLib.app_Znth1 0 l [x] i hi

theorem proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25 := by
  unfold energyNecklace_safety_wit_25
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have h := hb.2.2.1
  try dsimp [EnergyCellIndex] at h
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27 := by
  unfold energyNecklace_safety_wit_27
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hl := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds _ _ _ left PreH29 PreH31 ⟨by omega, by omega⟩
  have hk := EnergyValsDuplicated_label_bound__arithmetic_safety_bounds _ _ _ (split+1) PreH29 PreH31 ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> nlinarith

theorem proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31 := by
  unfold energyNecklace_safety_wit_31
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have h := hb.2.2.2.2
  try dsimp [EnergyCellIndex] at h
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32 := by
  unfold energyNecklace_safety_wit_32
  right
  intro dp_pre vals_pre n_pre beads_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have h := hb.2.2.2.1
  try dsimp [EnergyCellIndex] at h
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2 := by
  unfold energyNecklace_entail_wit_2
  right
  intro n_pre beads_l total width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | intro k hk; omega

theorem proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3 := by
  unfold energyNecklace_entail_wit_3
  right
  intro n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [Zlength_app, Zlength_cons, Zlength_nil, PreH9]
    omega

theorem proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4 := by
  unfold energyNecklace_entail_wit_4
  right
  intro vals_pre n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have he : i = n_pre := by omega
  simp only [he] at *
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5 := by
  unfold energyNecklace_entail_wit_5
  right
  intro vals_pre n_pre beads_l vals_l_2 total width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  simp only [Int.add_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | intro k hk; omega

theorem proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6 := by
  unfold energyNecklace_entail_wit_6
  right
  intro vals_pre n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hlen : Zlength (vals_l_2 ++ [Znth i beads_l 0]) = n_pre+(i+1) := by
    rw [Zlength_app, Zlength_cons, Zlength_nil, PreH9]; omega
  have hfirst : ∀ k, (0 ≤ k ∧ k < n_pre) → Znth k (vals_l_2++[Znth i beads_l 0]) 0 = Znth k beads_l 0 := by
    intro k hk
    rw [app_nth _ _ k (by rw [PreH9]; omega)]
    exact PreH12 k hk
  have hsecond : ∀ k, (0 ≤ k ∧ k < i+1) → Znth (n_pre+k) (vals_l_2++[Znth i beads_l 0]) 0 = Znth k beads_l 0 := by
    intro k hk
    by_cases he : k = i
    · subst k
      rw [app_Znth2 0 vals_l_2 _ (n_pre+i) (by rw [PreH9]), PreH9, Int.sub_self]
      rfl
    · rw [app_nth _ _ (n_pre+k) (by rw [PreH9]; omega)]
      exact PreH13 k ⟨hk.1, by omega⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (vals_l_2++[Znth i beads_l 0]) ?_
  rw [show n_pre+(i+1) = (n_pre+i)+1 by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7 := by
  unfold energyNecklace_entail_wit_7
  right
  intro vals_pre n_pre beads_l i vals_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have he : i = n_pre := by omega
  have hend : n_pre+i = total := by omega
  have hdup : EnergyValsDuplicated beads_l vals_l_2 n_pre :=
    ⟨by omega, PreH8, by omega, PreH12, fun k hk => PreH13 k ⟨hk.1, by omega⟩⟩
  rw [hend]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full vals_pre 0 total vals_l_2
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8 := by
  unfold energyNecklace_entail_wit_8
  right
  intro n_pre beads_l vals_l_2 total width PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | intro k hk; omega

theorem proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9 := by
  unfold energyNecklace_entail_wit_9
  right
  intro n_pre beads_l vals_l_2 i dp_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [Zlength_app, Zlength_cons, Zlength_nil, PreH9]
    omega

theorem proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10 := by
  unfold energyNecklace_entail_wit_10
  right
  intro dp_pre n_pre beads_l vals_l_2 i dp_l_2 width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have he : i = total*width := by omega
  have hz := EnergyZeroTable_from_prefix__prefix_table_bootstrap dp_l_2 total width i (by omega) PreH3 PreH1 PreH11 PreH9 PreH12
  have hd := EnergyZeroTable_len_done_2__prefix_table_bootstrap vals_l_2 dp_l_2 total width
    (by have := PreH13.2.2.1; omega) hz
  rw [he]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full dp_pre 0 (total*width) dp_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_energyNecklace_entail_wit_12 : energyNecklace_entail_wit_12 := by
  unfold energyNecklace_entail_wit_12
  right
  intro n_pre beads_l vals_l_2 dp_l_2 len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [←PreH2]
    exact ⟨PreH13, PreH8, by omega, fun l r idx hl _ _ _ => False.elim (by omega)⟩

theorem proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13 := by
  unfold energyNecklace_entail_wit_13
  right
  intro n_pre beads_l vals_l_2 dp_l_2 left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [←PreH2]
    exact ⟨PreH15, PreH8, PreH10, by omega, rfl, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14 := by
  unfold energyNecklace_entail_wit_14
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hb := PreH19.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15 := by
  unfold energyNecklace_entail_wit_15
  right
  intro n_pre beads_l vals_l_2 dp_l_2 best split right left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals rw [←PreH2]
    all_goals nlinarith

theorem proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16 := by
  unfold energyNecklace_entail_wit_16
  right
  intro n_pre beads_l vals_l dp_l total width len left right split best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hb := EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
    beads_l vals_l dp_l n_pre total width len left right split best 2100000000
    PreH32 PreH29 PreH1 PreH2 ⟨PreH7, PreH8⟩ ⟨PreH9, PreH10⟩ PreH11 ⟨PreH12, PreH13⟩ PreH28 PreH30
  have hc := hb.2.2.2.2
  dsimp [EnergyCellIndex] at hc
  rw [PreH2, PreH11] at hc
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_17_2 : energyNecklace_entail_wit_17_2 := by
  unfold energyNecklace_entail_wit_17_2
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hv := PreH27.1.1.2.2.1
  have hc : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate :=
    ⟨⟨PreH13, PreH14⟩, by omega, by dsimp [EnergyCellIndex]; omega⟩
  have hp := EnergySplitProgress_step_keep__dp_interval_progress _ _ _ _ _ _ _ _ _ _
    PreH12 ⟨PreH13, PreH14⟩ PreH27 hc PreH22 PreH1
  have hb := PreH27.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | omega
      | simpa only [PreH3, PreH2, PreH21] using hp

theorem proof_of_energyNecklace_entail_wit_17_1 : energyNecklace_entail_wit_17_1 := by
  unfold energyNecklace_entail_wit_17_1
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hv := PreH27.1.1.2.2.1
  have hc : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate :=
    ⟨⟨PreH13, PreH14⟩, by omega, by dsimp [EnergyCellIndex]; omega⟩
  have hp := EnergySplitProgress_step_take__dp_interval_progress _ _ _ _ _ _ _ _ _ _
    PreH12 ⟨PreH13, PreH14⟩ PreH27 hc ⟨PreH22, PreH23⟩ PreH1
  have hb := PreH27.2.2.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | omega
      | simpa only [PreH3, PreH2, PreH21] using hp

theorem proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19 := by
  unfold energyNecklace_entail_wit_19
  right
  intro n_pre beads_l vals_l_2 dp_l_2 best split right left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hv := PreH24.1.1.2.2.1
  have hm := EnergySplitProgress_finish_interval_best__dp_interval_progress _ _ _ _ _ _ _ _ _
    PreH12 PreH1 (by omega) PreH24
  have he : split = right := by omega
  rw [he] at PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | simpa only [PreH12] using hm
      | simpa only [PreH2, PreH12] using PreH24
      | rw [←PreH2]; nlinarith

theorem proof_of_energyNecklace_entail_wit_20 : energyNecklace_entail_wit_20 := by
  unfold energyNecklace_entail_wit_20
  right
  intro n_pre beads_l vals_l_2 dp_l total width len left right best PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hup : EnergyUpdatedCell vals_l_2 dp_l (replace_Znth (EnergyCellIndex width left right) best dp_l) width left right best :=
    ⟨⟨PreH13, by change left*width+right < Zlength dp_l; rw [PreH18]; exact PreH14⟩, rfl, PreH21⟩
  have hp := EnergyLeftProgress_step_update__dp_interval_progress _ _ _ _ _ _ _ _
    PreH11 PreH9 PreH10 PreH20 PreH21
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | simpa only [EnergyCellIndex, PreH2, PreH1, PreH11, PreH17] using hup
      | simpa only [EnergyCellIndex, PreH2, PreH1, PreH11, PreH17] using hp
      | simpa only [PreH17, PreH18, PreH1, PreH2, Zlength_replace_Znth]

theorem proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22 := by
  unfold energyNecklace_entail_wit_22
  right
  intro n_pre beads_l vals_l_2 dp_l_2 left len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hp := EnergyLeftProgress_finish_len__dp_interval_progress _ _ _ _ _ _ PreH1 PreH11 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    simpa only [PreH2] using hp

theorem proof_of_energyNecklace_entail_wit_24 : energyNecklace_entail_wit_24 := by
  unfold energyNecklace_entail_wit_24
  right
  intro n_pre beads_l vals_l_2 dp_l_2 len width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hl := EnergyLenDone_to_answer_len__answer_loop _ _ _ _ _ _ PreH1 PreH9 PreH13
  have hp : EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 0 :=
    ⟨PreH12, PreH11, PreH3, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | simpa only [PreH2] using hp | simpa only [PreH2] using hl

theorem proof_of_energyNecklace_entail_wit_25 : energyNecklace_entail_wit_25 := by
  unfold energyNecklace_entail_wit_25
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hb := EnergyAnswerProgress_answer_bounds__answer_loop _ _ _ _ _ _ _ _ PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_26_split_goal_1 : energyNecklace_entail_wit_26_split_goal_1 := by
  unfold energyNecklace_entail_wit_26_split_goal_1
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := EnergyLenDone_rotation_cell_best__answer_loop _ _ _ _ _ _ PreH4 PreH2 PreH3 ⟨PreH8, PreH1⟩ PreH15
  convert hb using 1 <;> dsimp [EnergyCellIndex] <;> congr 1 <;> omega

theorem proof_of_energyNecklace_entail_wit_26_split_goal_2 : energyNecklace_entail_wit_26_split_goal_2 := by
  unfold energyNecklace_entail_wit_26_split_goal_2
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [←PreH2]
  nlinarith

theorem proof_of_energyNecklace_entail_wit_26 : energyNecklace_entail_wit_26 := by
  unfold energyNecklace_entail_wit_26
  right
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_energyNecklace_entail_wit_26_split_goal_1 n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
      | exact proof_of_energyNecklace_entail_wit_26_split_goal_2 n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_energyNecklace_entail_wit_27 : energyNecklace_entail_wit_27 := by
  unfold energyNecklace_entail_wit_27
  right
  intro n_pre beads_l vals_l_2 dp_l total width start answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hb := EnergyAnswerCellBounded__answer_loop _ _ _ _ _ _ _ PreH18 PreH13 PreH1 PreH2 ⟨PreH7, PreH8⟩ PreH12 PreH14
  dsimp [EnergyCellIndex] at hb
  rw [PreH2] at hb
  have he : start*total+(start+n_pre-1) = start*total+start+n_pre-1 := by omega
  rw [he] at hb
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals omega

theorem proof_of_energyNecklace_entail_wit_28_2 : energyNecklace_entail_wit_28_2 := by
  unfold energyNecklace_entail_wit_28_2
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hp := EnergyAnswerProgress_step_keep__answer_loop _ _ _ _ _ _ _ _ _
    PreH17 ⟨PreH8, PreH9⟩ PreH18 PreH11 PreH1
  have hb := EnergyAnswerProgress_answer_bounds__answer_loop _ _ _ _ _ _ _ _ PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | simpa only [PreH3, PreH2] using hp | omega

theorem proof_of_energyNecklace_entail_wit_28_1 : energyNecklace_entail_wit_28_1 := by
  unfold energyNecklace_entail_wit_28_1
  right
  intro n_pre beads_l vals_l_2 dp_l_2 total width start value answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hp := EnergyAnswerProgress_step_update__answer_loop _ _ _ _ _ _ _ _ _
    PreH17 ⟨PreH8, PreH9⟩ PreH18 ⟨PreH11, PreH12⟩ PreH1
  have hb := EnergyAnswerProgress_answer_bounds__answer_loop _ _ _ _ _ _ _ _ PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | simpa only [PreH3, PreH2] using hp | omega

theorem proof_of_energyNecklace_entail_wit_30 : energyNecklace_entail_wit_30 := by
  unfold energyNecklace_entail_wit_30
  right
  intro n_pre beads_l vals_l_2 dp_l_2 answer start width total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact EnergyAnswerProgress_finish__answer_loop _ _ _ _ _ _ _ _ PreH4 PreH16 PreH1 PreH9

theorem proof_of_energyNecklace_return_wit_1 : energyNecklace_return_wit_1 := by
  unfold energyNecklace_return_wit_1
  right
  intro dp_pre vals_pre n_pre beads_l vals_l_2 dp_l_2 total width answer PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hp : EnergyLenDone vals_l_2 dp_l_2 (2*n_pre) (2*n_pre) (n_pre+1) := by
    simpa only [PreH2, PreH1] using PreH12
  rw [PreH2, PreH1]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_l_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_manual
