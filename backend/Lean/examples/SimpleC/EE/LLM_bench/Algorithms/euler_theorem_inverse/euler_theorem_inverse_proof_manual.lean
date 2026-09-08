import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_goal
import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open euler_theorem_inverse_goal euler_theorem_inverse_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_euler_phi_entail_wit_1_split_goal_1 : euler_phi_entail_wit_1_split_goal_1 := by
  unfold euler_phi_entail_wit_1_split_goal_1
  intro value_pre PreH1 PreH2
  refine ⟨⟨⟨1,by simp⟩,?_⟩,?_⟩
  · intro op rp ho hr
    unfold EulerPhi at ho hr
    rw [ho,hr]
    grind
  · intro p hp hl _
    have := hp.1
    omega

theorem proof_of_euler_phi_entail_wit_1 : euler_phi_entail_wit_1 := by
  unfold euler_phi_entail_wit_1
  right
  intro value_pre PreH1 PreH2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_1_split_goal_1 value_pre PreH1 PreH2))
    | exact (proof_of_euler_phi_entail_wit_1_split_goal_1 value_pre PreH1 PreH2)
    | trivial

theorem proof_of_euler_phi_entail_wit_2_split_goal_1 : euler_phi_entail_wit_2_split_goal_1 := by
  unfold euler_phi_entail_wit_2_split_goal_1
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hm : Z.modulo value factor=0 := Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 ((Z.rem_divide value factor (by omega)).1 PreH1))
  exact euler_phi_removal_start__euler_phi_setup_removal value_pre factor value result PreH3 PreH5 PreH7 PreH9 hm PreH13

theorem proof_of_euler_phi_entail_wit_2 : euler_phi_entail_wit_2 := by
  unfold euler_phi_entail_wit_2
  right
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_2_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_euler_phi_entail_wit_2_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_euler_phi_entail_wit_3_split_goal_1 : euler_phi_entail_wit_3_split_goal_1 := by
  unfold euler_phi_entail_wit_3_split_goal_1
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hm : Z.modulo value factor=0 := Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 ((Z.rem_divide value factor (by omega)).1 PreH1))
  rewrite [show Z.quot value factor=Z.div value factor from (Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)).symm]
  rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
  have hs : Z.pow factor (removed+1)=Z.pow factor removed*factor := by
    cases removed with
    | ofNat m => exact Int.pow_succ factor m
    | negSucc m => omega
  have hdiv := Int.fmod_add_mul_fdiv value factor
  change value.fmod factor=0 at hm
  rw [hm] at hdiv
  refine ⟨before,removed+1,by omega,?_,hfb,hfr,hprogress,?_⟩
  · rw [hs]
    change before=value.fdiv factor*(Z.pow factor removed*factor)
    grind
  · exact EulerPhiFactorCompletion_divide value_pre factor value result (by omega) hm hcompletion

theorem proof_of_euler_phi_entail_wit_3_split_goal_2 : euler_phi_entail_wit_3_split_goal_2 := by
  unfold euler_phi_entail_wit_3_split_goal_2
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  apply Z.quot_le_upper_bound value factor value_pre (by omega)
  have hm := Int.mul_le_mul_of_nonneg_right (by omega : 1≤factor) (by omega : 0≤value_pre)
  omega

theorem proof_of_euler_phi_entail_wit_3_split_goal_3 : euler_phi_entail_wit_3_split_goal_3 := by
  unfold euler_phi_entail_wit_3_split_goal_3
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hd := (Z.rem_divide value factor (by omega)).1 PreH1
  exact (euler_exact_positive_quotient_bounds__euler_phi_factor_completion value factor PreH4 PreH8 hd).1

theorem proof_of_euler_phi_entail_wit_3 : euler_phi_entail_wit_3 := by
  unfold euler_phi_entail_wit_3
  right
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_3_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_3_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_3_split_goal_2 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_3_split_goal_2 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_3_split_goal_3 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_3_split_goal_3 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | trivial

theorem proof_of_euler_phi_entail_wit_4_split_goal_1 : euler_phi_entail_wit_4_split_goal_1 := by
  unfold euler_phi_entail_wit_4_split_goal_1
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
  have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
  change _≤2147483647
  omega

theorem proof_of_euler_phi_entail_wit_4_split_goal_2 : euler_phi_entail_wit_4_split_goal_2 := by
  unfold euler_phi_entail_wit_4_split_goal_2
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
  have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
  omega

theorem proof_of_euler_phi_entail_wit_4_split_goal_3 : euler_phi_entail_wit_4_split_goal_3 := by
  unfold euler_phi_entail_wit_4_split_goal_3
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
  have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
  exact hb.2.1

theorem proof_of_euler_phi_entail_wit_4_split_goal_4 : euler_phi_entail_wit_4_split_goal_4 := by
  unfold euler_phi_entail_wit_4_split_goal_4
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
  have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
  exact hb.1

theorem proof_of_euler_phi_entail_wit_4_split_goal_5 : euler_phi_entail_wit_4_split_goal_5 := by
  unfold euler_phi_entail_wit_4_split_goal_5
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
  exact (Z.rem_divide result factor (by omega)).2 hfr

theorem proof_of_euler_phi_entail_wit_4 : euler_phi_entail_wit_4 := by
  unfold euler_phi_entail_wit_4
  right
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_4_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_4_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_4_split_goal_2 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_4_split_goal_2 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_4_split_goal_3 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_4_split_goal_3 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_4_split_goal_4 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_4_split_goal_4 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_4_split_goal_5 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | exact (proof_of_euler_phi_entail_wit_4_split_goal_5 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | trivial

theorem proof_of_euler_phi_entail_wit_5_1_split_goal_1 : euler_phi_entail_wit_5_1_split_goal_1 := by
  unfold euler_phi_entail_wit_5_1_split_goal_1
  intro value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact euler_completed_progress__euler_phi_factor_completion value_pre factor value result PreH3 PreH5 PreH7 PreH9 PreH15

theorem proof_of_euler_phi_entail_wit_5_1_split_goal_2 : euler_phi_entail_wit_5_1_split_goal_2 := by
  unfold euler_phi_entail_wit_5_1_split_goal_2
  intro value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact euler_active_frontier_bound__euler_phi_factor_completion value_pre factor value result PreH7 PreH8 PreH15

theorem proof_of_euler_phi_entail_wit_5_1 : euler_phi_entail_wit_5_1 := by
  unfold euler_phi_entail_wit_5_1
  right
  intro value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_5_1_split_goal_1 value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_euler_phi_entail_wit_5_1_split_goal_1 value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_5_1_split_goal_2 value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_euler_phi_entail_wit_5_1_split_goal_2 value_pre value result factor PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | trivial

theorem proof_of_euler_phi_entail_wit_5_2_split_goal_1 : euler_phi_entail_wit_5_2_split_goal_1 := by
  unfold euler_phi_entail_wit_5_2_split_goal_1
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact euler_progress_advance_nondivisor__euler_phi_factor_completion value_pre factor value result PreH9 PreH1 PreH13

theorem proof_of_euler_phi_entail_wit_5_2 : euler_phi_entail_wit_5_2 := by
  unfold euler_phi_entail_wit_5_2
  right
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_5_2_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_euler_phi_entail_wit_5_2_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_euler_phi_entail_wit_6 : euler_phi_entail_wit_6 := by
  unfold euler_phi_entail_wit_6
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hd := PreH12.1.1
  have hr := (Z.rem_divide result value (by omega)).2 hd
  by_cases he : value=1
  · Right
    Exists factor
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first | exact PreH12 | (change _≤2147483647; omega) | omega | trivial
  · have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result value PreH6 (by omega) hd
    Left
    Exists factor
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first | exact PreH12 | (change _≤2147483647; omega) | omega | trivial

theorem proof_of_euler_phi_return_wit_1_split_goal_1 : euler_phi_return_wit_1_split_goal_1 := by
  unfold euler_phi_return_wit_1_split_goal_1
  intro value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact euler_progress_terminal_prime__euler_phi_final_results value_pre frontier value result (by omega) PreH8 PreH12 PreH18

theorem proof_of_euler_phi_return_wit_1 : euler_phi_return_wit_1 := by
  unfold euler_phi_return_wit_1
  right
  intro value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_return_wit_1_split_goal_1 value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_euler_phi_return_wit_1_split_goal_1 value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_euler_phi_return_wit_2_split_goal_1 : euler_phi_return_wit_2_split_goal_1 := by
  unfold euler_phi_return_wit_2_split_goal_1
  intro value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact euler_progress_terminal_one__euler_phi_final_results value_pre frontier value result PreH1 PreH18

theorem proof_of_euler_phi_return_wit_2 : euler_phi_return_wit_2 := by
  unfold euler_phi_return_wit_2
  right
  intro value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_return_wit_2_split_goal_1 value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_euler_phi_return_wit_2_split_goal_1 value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_euler_phi_return_wit_3_split_goal_1 : euler_phi_return_wit_3_split_goal_1 := by
  unfold euler_phi_return_wit_3_split_goal_1
  intro value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact euler_progress_terminal_one__euler_phi_final_results value_pre frontier value result PreH1 PreH14

theorem proof_of_euler_phi_return_wit_3 : euler_phi_return_wit_3 := by
  unfold euler_phi_return_wit_3
  right
  intro value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_phi_return_wit_3_split_goal_1 value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | exact (proof_of_euler_phi_return_wit_3_split_goal_1 value_pre frontier value result PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
    | trivial

theorem proof_of_modular_power_entail_wit_1_split_goal_1 : modular_power_entail_wit_1_split_goal_1 := by
  unfold modular_power_entail_wit_1_split_goal_1
  intro modulus_pre exponent_pre base_pre PreH1 PreH2 PreH3 PreH4 PreH5
  unfold EulerModularPowerProgress
  simp

theorem proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1 := by
  unfold modular_power_entail_wit_1
  right
  intro modulus_pre exponent_pre base_pre PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_1_split_goal_1 modulus_pre exponent_pre base_pre PreH1 PreH2 PreH3 PreH4 PreH5))
    | exact (proof_of_modular_power_entail_wit_1_split_goal_1 modulus_pre exponent_pre base_pre PreH1 PreH2 PreH3 PreH4 PreH5)
    | trivial

theorem proof_of_modular_power_entail_wit_2_1_split_goal_1 : modular_power_entail_wit_2_1_split_goal_1 := by
  unfold modular_power_entail_wit_2_1_split_goal_1
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [AUXLib.rem_eq_mod exponent 2 PreH10 (by omega)] at PreH1
  rw [AUXLib.rem_eq_mod (base*base) modulus_pre PreH14 (by omega)]
  rw [show Z.quot exponent 2=Z.div exponent 2 from (Int.fdiv_eq_tdiv_of_nonneg PreH10 (by omega)).symm]
  rw [AUXLib.rem_eq_mod (result*base) modulus_pre PreH16 (by omega)]
  exact euler_modular_progress_odd_step__modular_power_loop base_pre exponent_pre modulus_pre base exponent result (by omega) PreH2 PreH1 PreH18

theorem proof_of_modular_power_entail_wit_2_1_split_goal_2 : modular_power_entail_wit_2_1_split_goal_2 := by
  unfold modular_power_entail_wit_2_1_split_goal_2
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  change _≤2147483647
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_3 : modular_power_entail_wit_2_1_split_goal_3 := by
  unfold modular_power_entail_wit_2_1_split_goal_3
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_4 : modular_power_entail_wit_2_1_split_goal_4 := by
  unfold modular_power_entail_wit_2_1_split_goal_4
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  change _≤2147483647
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_5 : modular_power_entail_wit_2_1_split_goal_5 := by
  unfold modular_power_entail_wit_2_1_split_goal_5
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_6 : modular_power_entail_wit_2_1_split_goal_6 := by
  unfold modular_power_entail_wit_2_1_split_goal_6
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_7 : modular_power_entail_wit_2_1_split_goal_7 := by
  unfold modular_power_entail_wit_2_1_split_goal_7
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_8 : modular_power_entail_wit_2_1_split_goal_8 := by
  unfold modular_power_entail_wit_2_1_split_goal_8
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_9 : modular_power_entail_wit_2_1_split_goal_9 := by
  unfold modular_power_entail_wit_2_1_split_goal_9
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_10 : modular_power_entail_wit_2_1_split_goal_10 := by
  unfold modular_power_entail_wit_2_1_split_goal_10
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_11 : modular_power_entail_wit_2_1_split_goal_11 := by
  unfold modular_power_entail_wit_2_1_split_goal_11
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1 := by
  unfold modular_power_entail_wit_2_1
  right
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_1 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_1 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_2 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_2 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_3 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_3 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_4 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_4 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_5 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_5 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_6 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_6 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_7 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_7 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_8 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_8 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_9 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_9 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_10 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_10 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_1_split_goal_11 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_11 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_modular_power_entail_wit_2_2_split_goal_1 : modular_power_entail_wit_2_2_split_goal_1 := by
  unfold modular_power_entail_wit_2_2_split_goal_1
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [AUXLib.rem_eq_mod exponent 2 PreH10 (by omega)] at PreH1
  rw [AUXLib.rem_eq_mod (base*base) modulus_pre PreH14 (by omega)]
  rw [show Z.quot exponent 2=Z.div exponent 2 from (Int.fdiv_eq_tdiv_of_nonneg PreH10 (by omega)).symm]
  exact euler_modular_progress_even_step__modular_power_loop base_pre exponent_pre modulus_pre base exponent result (by omega) PreH2 PreH1 PreH18

theorem proof_of_modular_power_entail_wit_2_2_split_goal_2 : modular_power_entail_wit_2_2_split_goal_2 := by
  unfold modular_power_entail_wit_2_2_split_goal_2
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  change _≤2147483647
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_3 : modular_power_entail_wit_2_2_split_goal_3 := by
  unfold modular_power_entail_wit_2_2_split_goal_3
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_4 : modular_power_entail_wit_2_2_split_goal_4 := by
  unfold modular_power_entail_wit_2_2_split_goal_4
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  change _≤2147483647
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_5 : modular_power_entail_wit_2_2_split_goal_5 := by
  unfold modular_power_entail_wit_2_2_split_goal_5
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_6 : modular_power_entail_wit_2_2_split_goal_6 := by
  unfold modular_power_entail_wit_2_2_split_goal_6
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_7 : modular_power_entail_wit_2_2_split_goal_7 := by
  unfold modular_power_entail_wit_2_2_split_goal_7
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_8 : modular_power_entail_wit_2_2_split_goal_8 := by
  unfold modular_power_entail_wit_2_2_split_goal_8
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_9 : modular_power_entail_wit_2_2_split_goal_9 := by
  unfold modular_power_entail_wit_2_2_split_goal_9
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
  have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
  have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
  have hql := Z.quot_pos exponent 2 PreH10 (by omega)
  have hqu := Z.quot_le_upper_bound exponent 2 exponent_pre (by omega) (by omega)
  omega

theorem proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2 := by
  unfold modular_power_entail_wit_2_2
  right
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_1 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_1 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_2 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_2 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_3 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_3 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_4 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_4 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_5 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_5 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_6 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_6 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_7 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_7 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_8 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_8 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_2_2_split_goal_9 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_9 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | trivial

theorem proof_of_modular_power_return_wit_1_split_goal_1 : modular_power_return_wit_1_split_goal_1 := by
  unfold modular_power_return_wit_1_split_goal_1
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : exponent=0 := by omega
  subst exponent
  exact euler_modular_progress_zero_finish__modular_power_final base_pre exponent_pre modulus_pre base result PreH11 PreH12 PreH17

theorem proof_of_modular_power_return_wit_1 : modular_power_return_wit_1 := by
  unfold modular_power_return_wit_1
  right
  intro modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_modular_power_return_wit_1_split_goal_1 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))
    | exact (proof_of_modular_power_return_wit_1_split_goal_1 modulus_pre exponent_pre base_pre result exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | trivial

theorem proof_of_euler_theorem_inverse_entail_wit_1_split_goal_1 : euler_theorem_inverse_entail_wit_1_split_goal_1 := by
  unfold euler_theorem_inverse_entail_wit_1_split_goal_1
  intro modulus_pre value_pre retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  simpa using PreH3

theorem proof_of_euler_theorem_inverse_entail_wit_1 : euler_theorem_inverse_entail_wit_1 := by
  unfold euler_theorem_inverse_entail_wit_1
  right
  intro modulus_pre value_pre retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_theorem_inverse_entail_wit_1_split_goal_1 modulus_pre value_pre retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8))
    | exact (proof_of_euler_theorem_inverse_entail_wit_1_split_goal_1 modulus_pre value_pre retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    | trivial

theorem proof_of_euler_theorem_inverse_return_wit_1_split_goal_1 : euler_theorem_inverse_return_wit_1_split_goal_1 := by
  unfold euler_theorem_inverse_return_wit_1_split_goal_1
  intro modulus_pre value_pre exponent retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact (euler_totient_inverse_theorem__inverse_final_result value_pre modulus_pre (exponent+1) retval PreH4 PreH5 PreH6 PreH8 PreH11 (by simpa using PreH3)).2

theorem proof_of_euler_theorem_inverse_return_wit_1 : euler_theorem_inverse_return_wit_1 := by
  unfold euler_theorem_inverse_return_wit_1
  right
  intro modulus_pre value_pre exponent retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_euler_theorem_inverse_return_wit_1_split_goal_1 modulus_pre value_pre exponent retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_euler_theorem_inverse_return_wit_1_split_goal_1 modulus_pre value_pre exponent retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_proof_manual
