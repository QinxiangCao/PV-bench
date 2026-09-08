import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal
import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open rod_cutting_goal rod_cutting_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_rod_cutting_entail_wit_2_split_goal_1 : rod_cutting_entail_wit_2_split_goal_1 := by
  unfold rod_cutting_entail_wit_2_split_goal_1
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH11

theorem proof_of_rod_cutting_entail_wit_2_split_goal_2 : rod_cutting_entail_wit_2_split_goal_2 := by
  unfold rod_cutting_entail_wit_2_split_goal_2
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact Or.inr ⟨fun piece hp => False.elim (by omega), rfl⟩

theorem proof_of_rod_cutting_entail_wit_2_split_goal_3 : rod_cutting_entail_wit_2_split_goal_3 := by
  unfold rod_cutting_entail_wit_2_split_goal_3
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH6

theorem proof_of_rod_cutting_entail_wit_4_1_split_goal_1 : rod_cutting_entail_wit_4_1_split_goal_1 := by
  unfold rod_cutting_entail_wit_4_1_split_goal_1
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [Int.sub_zero] at PreH1 ⊢
  apply rod_cut_scan_best_step__scan_transitions _ i best _ PreH16 PreH22
  left
  exact ⟨by omega, rfl⟩

theorem proof_of_rod_cutting_entail_wit_4_2_split_goal_1 : rod_cutting_entail_wit_4_2_split_goal_1 := by
  unfold rod_cutting_entail_wit_4_2_split_goal_1
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [Int.sub_zero] at PreH1 ⊢
  apply rod_cut_scan_best_step__scan_transitions _ i best _ PreH16 PreH22
  right
  exact ⟨by omega, rfl⟩

theorem proof_of_rod_cutting_entail_wit_5_split_goal_1 : rod_cutting_entail_wit_5_split_goal_1 := by
  unfold rod_cutting_entail_wit_5_split_goal_1
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro k hk
  by_cases hlt : k < j
  · have hn : Znth k (revenue_l_2 ++ [best]) 0 = Znth k revenue_l_2 0 :=
      ListLib.app_Znth1 0 revenue_l_2 [best] k ⟨hk.1, by change k < Zlength revenue_l_2; omega⟩
    rw [hn]
    exact PreH16 k ⟨hk.1, hlt⟩
  · have he : k = j := by omega
    subst k
    rw [app_Znth2 0 revenue_l_2 [best] j (by omega), PreH13, Int.sub_self]
    exact ⟨PreH11, PreH12⟩

theorem proof_of_rod_cutting_entail_wit_5_split_goal_2 : rod_cutting_entail_wit_5_split_goal_2 := by
  unfold rod_cutting_entail_wit_5_split_goal_2
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he : i = j + 1 := by omega
  subst i
  exact rod_cut_revenue_table_snoc__table_extension price_l revenue_l_2 j best
    PreH7 PreH13 (PreH6 j (by omega)).1 PreH14 PreH15

theorem proof_of_rod_cutting_entail_wit_5_split_goal_3 : rod_cutting_entail_wit_5_split_goal_3 := by
  unfold rod_cutting_entail_wit_5_split_goal_3
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  rw [Zlength_app, Zlength_cons, Zlength_nil, PreH13]
  omega

theorem proof_of_rod_cutting_entail_wit_5_split_goal_4 : rod_cutting_entail_wit_5_split_goal_4 := by
  unfold rod_cutting_entail_wit_5_split_goal_4
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH6

theorem proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1 := by
  unfold rod_cutting_entail_wit_1
  right
  intro n_pre revenue_pre price_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([0] : List Int) ?_
  split_pure_spatial
  · exact intArray.seg_single revenue_pre 0 (0 : Int)
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | rfl | omega
    · intro n hn
      have he : n = 0 := by omega
      subst n
      decide
    · intro k hk
      have he : k = 0 := by omega
      subst k
      exact rod_cut_optimal_revenue_zero__boundary_states price_l

theorem proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2 := by
  unfold rod_cutting_entail_wit_2
  right
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_rod_cutting_entail_wit_2_split_goal_1 n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_rod_cutting_entail_wit_2_split_goal_2 n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_rod_cutting_entail_wit_2_split_goal_3 n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_rod_cutting_entail_wit_4_1 : rod_cutting_entail_wit_4_1 := by
  unfold rod_cutting_entail_wit_4_1
  right
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_rod_cutting_entail_wit_4_1_split_goal_1 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_rod_cutting_entail_wit_4_2 : rod_cutting_entail_wit_4_2 := by
  unfold rod_cutting_entail_wit_4_2
  right
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_rod_cutting_entail_wit_4_2_split_goal_1 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5 := by
  unfold rod_cutting_entail_wit_5
  right
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_rod_cutting_entail_wit_5_split_goal_1 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_rod_cutting_entail_wit_5_split_goal_2 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_rod_cutting_entail_wit_5_split_goal_3 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact proof_of_rod_cutting_entail_wit_5_split_goal_4 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_rod_cutting_return_wit_1 : rod_cutting_return_wit_1 := by
  unfold rod_cutting_return_wit_1
  right
  intro n_pre revenue_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : j = n_pre + 1 := by omega
  rw [he] at PreH9 PreH10 PreH11 ⊢
  refine Automation.exp_right_rule (CRules := naive_C_Rules) revenue_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using
      intArray.seg_to_full revenue_pre 0 (n_pre + 1) revenue_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | simpa only [Int.sub_zero]

end SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_manual
