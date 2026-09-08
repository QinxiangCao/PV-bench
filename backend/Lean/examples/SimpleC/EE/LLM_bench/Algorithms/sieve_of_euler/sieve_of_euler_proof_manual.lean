import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_goal
import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open sieve_of_euler_goal sieve_of_euler_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem product_bound (i p : Int) (hi : 0≤i) (hin : i≤46340)
    (hp : 2≤p) (hpi : p≤i) : i*p≤INT_MAX := by
  have h1 := Int.mul_le_mul_of_nonneg_left hpi hi
  have h2 := Int.mul_le_mul_of_nonneg_left hin hi
  have h3 := Int.mul_le_mul_of_nonneg_right hin (by omega : (0:Int)≤46340)
  change i*p≤2147483647
  omega

theorem proof_of_get_prime_entail_wit_1_split_goal_1 : get_prime_entail_wit_1_split_goal_1 := by
  unfold get_prime_entail_wit_1_split_goal_1
  intro n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4
  exact EulerInitPrefix_start__core_invariants n_pre flag0 PreH3

theorem proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1 := by
  unfold get_prime_entail_wit_1
  right
  intro n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_1_split_goal_1 n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_get_prime_entail_wit_1_split_goal_1 n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4)
    | trivial

theorem proof_of_get_prime_entail_wit_2_split_goal_1 : get_prime_entail_wit_2_split_goal_1 := by
  unfold get_prime_entail_wit_2_split_goal_1
  intro n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact EulerInitPrefix_step__core_invariants n_pre i flag_l_2 PreH1 PreH5 PreH7

theorem proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2 := by
  unfold get_prime_entail_wit_2
  right
  intro n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_2_split_goal_1 n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7))
    | exact (proof_of_get_prime_entail_wit_2_split_goal_1 n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    | trivial

theorem proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3 := by
  unfold get_prime_entail_wit_3
  left
  intro prime_pre flag_pre n_pre prime0 flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  subst tot
  prop_apply (naive_C_Rules.IntArray.seg_Zlength prime_pre 1 (n_pre+1) prime0)
  Intros_p hlen
  Exists flag_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact EulerInitPrefix_finish_outer__core_invariants n_pre i flag_l_2 prime0 PreH1 PreH3 (by omega) PreH7
    | omega
    | trivial

theorem proof_of_get_prime_entail_wit_5_1_split_goal_1 : get_prime_entail_wit_5_1_split_goal_1 := by
  unfold get_prime_entail_wit_5_1_split_goal_1
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
  exact product_bound i _ (by omega) (by omega) hb.1 hb.2

theorem proof_of_get_prime_entail_wit_5_1_split_goal_2 : get_prime_entail_wit_5_1_split_goal_2 := by
  unfold get_prime_entail_wit_5_1_split_goal_2
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
  exact hb.2

theorem proof_of_get_prime_entail_wit_5_1_split_goal_3 : get_prime_entail_wit_5_1_split_goal_3 := by
  unfold get_prime_entail_wit_5_1_split_goal_3
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
  exact hb.1

theorem proof_of_get_prime_entail_wit_5_1_split_goal_4 : get_prime_entail_wit_5_1_split_goal_4 := by
  unfold get_prime_entail_wit_5_1_split_goal_4
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact EulerOuterState_self_inner_start__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9

theorem proof_of_get_prime_entail_wit_5_1 : get_prime_entail_wit_5_1 := by
  unfold get_prime_entail_wit_5_1
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_get_prime_entail_wit_5_2_split_goal_1 : get_prime_entail_wit_5_2_split_goal_1 := by
  unfold get_prime_entail_wit_5_2_split_goal_1
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).2
  exact product_bound i _ (by omega) (by omega) hb.1 hb.2

theorem proof_of_get_prime_entail_wit_5_2_split_goal_2 : get_prime_entail_wit_5_2_split_goal_2 := by
  unfold get_prime_entail_wit_5_2_split_goal_2
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).2
  exact hb.2

theorem proof_of_get_prime_entail_wit_5_2_split_goal_3 : get_prime_entail_wit_5_2_split_goal_3 := by
  unfold get_prime_entail_wit_5_2_split_goal_3
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).2
  exact hb.1

theorem proof_of_get_prime_entail_wit_5_2_split_goal_4 : get_prime_entail_wit_5_2_split_goal_4 := by
  unfold get_prime_entail_wit_5_2_split_goal_4
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact EulerOuterState_nonself_inner_start__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9

theorem proof_of_get_prime_entail_wit_5_2_split_goal_5 : get_prime_entail_wit_5_2_split_goal_5 := by
  unfold get_prime_entail_wit_5_2_split_goal_5
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).1

theorem proof_of_get_prime_entail_wit_5_2 : get_prime_entail_wit_5_2 := by
  unfold get_prime_entail_wit_5_2
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_5 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_5 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_get_prime_entail_wit_7_split_goal_1 : get_prime_entail_wit_7_split_goal_1 := by
  unfold get_prime_entail_wit_7_split_goal_1
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact EulerInnerState_mark_product__core_invariants n_pre i j tot flag_l_2 prime_l_2 PreH5 PreH6 PreH9 PreH10 PreH2 PreH11

theorem proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7 := by
  unfold get_prime_entail_wit_7
  right
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_7_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | exact (proof_of_get_prime_entail_wit_7_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
    | trivial

theorem proof_of_get_prime_entail_wit_8_split_goal_1 : get_prime_entail_wit_8_split_goal_1 := by
  unfold get_prime_entail_wit_8_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH11.2.2.2.2.2.1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).1 PreH1)

theorem proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8 := by
  unfold get_prime_entail_wit_8
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_8_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_8_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_get_prime_entail_wit_9_split_goal_1 : get_prime_entail_wit_9_split_goal_1 := by
  unfold get_prime_entail_wit_9_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  have hle := hnext.2.2.2.2.2.1
  have hb := hnext.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega,hle⟩
  simp only [Int.add_sub_cancel] at hb
  exact product_bound i _ (by omega) (by omega) hb.1 hb.2

theorem proof_of_get_prime_entail_wit_9_split_goal_2 : get_prime_entail_wit_9_split_goal_2 := by
  unfold get_prime_entail_wit_9_split_goal_2
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  have hle := hnext.2.2.2.2.2.1
  have hb := hnext.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega,hle⟩
  simp only [Int.add_sub_cancel] at hb
  exact hb.2

theorem proof_of_get_prime_entail_wit_9_split_goal_3 : get_prime_entail_wit_9_split_goal_3 := by
  unfold get_prime_entail_wit_9_split_goal_3
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  have hle := hnext.2.2.2.2.2.1
  have hb := hnext.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega,hle⟩
  simp only [Int.add_sub_cancel] at hb
  exact hb.1

theorem proof_of_get_prime_entail_wit_9_split_goal_4 : get_prime_entail_wit_9_split_goal_4 := by
  unfold get_prime_entail_wit_9_split_goal_4
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  exact hnext

theorem proof_of_get_prime_entail_wit_9_split_goal_5 : get_prime_entail_wit_9_split_goal_5 := by
  unfold get_prime_entail_wit_9_split_goal_5
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  exact hnext.2.2.2.2.2.1

theorem proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9 := by
  unfold get_prime_entail_wit_9
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_4 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_4 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_5 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_5 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_get_prime_entail_wit_10_split_goal_1 : get_prime_entail_wit_10_split_goal_1 := by
  unfold get_prime_entail_wit_10_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa using PreH12

theorem proof_of_get_prime_entail_wit_10_split_goal_2 : get_prime_entail_wit_10_split_goal_2 := by
  unfold get_prime_entail_wit_10_split_goal_2
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa using PreH11

theorem proof_of_get_prime_entail_wit_10_split_goal_3 : get_prime_entail_wit_10_split_goal_3 := by
  unfold get_prime_entail_wit_10_split_goal_3
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa using PreH10

theorem proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10 := by
  unfold get_prime_entail_wit_10
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_10_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))
    | exact (proof_of_get_prime_entail_wit_10_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_10_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))
    | exact (proof_of_get_prime_entail_wit_10_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_10_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))
    | exact (proof_of_get_prime_entail_wit_10_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
    | trivial

theorem proof_of_get_prime_entail_wit_11_1_split_goal_1 : get_prime_entail_wit_11_1_split_goal_1 := by
  unfold get_prime_entail_wit_11_1_split_goal_1
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH10.2.2.2.2.2.2.2.2.2.2.2.2.2 PreH1

theorem proof_of_get_prime_entail_wit_11_1_split_goal_2 : get_prime_entail_wit_11_1_split_goal_2 := by
  unfold get_prime_entail_wit_11_1_split_goal_2
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH10.2.2.2.2.2.2.2.2.1

theorem proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1 := by
  unfold get_prime_entail_wit_11_1
  right
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_11_1_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_11_1_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_11_1_split_goal_2 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_11_1_split_goal_2 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_get_prime_entail_wit_11_2_split_goal_1 : get_prime_entail_wit_11_2_split_goal_1 := by
  unfold get_prime_entail_wit_11_2_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH11.2.2.2.2.2.1

theorem proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2 := by
  unfold get_prime_entail_wit_11_2
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_11_2_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_get_prime_entail_wit_11_2_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | trivial

theorem proof_of_get_prime_entail_wit_13_split_goal_1 : get_prime_entail_wit_13_split_goal_1 := by
  unfold get_prime_entail_wit_13_split_goal_1
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : n_pre+1=i := by omega
  rw [he]
  exact PreH8

theorem proof_of_get_prime_entail_wit_13 : get_prime_entail_wit_13 := by
  unfold get_prime_entail_wit_13
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_13_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8))
    | exact (proof_of_get_prime_entail_wit_13_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    | trivial

theorem proof_of_get_prime_which_implies_wit_1_split_goal_1 : get_prime_which_implies_wit_1_split_goal_1 := by
  unfold get_prime_which_implies_wit_1_split_goal_1
  intro n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5
  rcases PreH5 with ⟨hf,hlen,hlo,hhi,ht0,htlt,hp,hb⟩
  refine ⟨hf.1,hlen,ht0,by omega,⟨hf.1,?_⟩,by simpa using hp⟩
  intro k hk
  exact (hf.2 k hk).1 (by omega)

theorem proof_of_get_prime_which_implies_wit_1 : get_prime_which_implies_wit_1 := by
  unfold get_prime_which_implies_wit_1
  right
  intro n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_which_implies_wit_1_split_goal_1 n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5))
    | exact (proof_of_get_prime_which_implies_wit_1_split_goal_1 n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5)
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_proof_manual
