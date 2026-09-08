import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_goal
import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open sliding_window_maximum_goal sliding_window_maximum_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 : maxSlidingWindow_entail_wit_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_1
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro pos hp
  omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 : maxSlidingWindow_entail_wit_1_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_2
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pos hp; omega
  · intro p q hpq; omega
  · intro p q hpq; omega
  · intro idx hidx hw; omega
  · intro h; omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 : maxSlidingWindow_entail_wit_1_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_3
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro pos hp
  omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 : maxSlidingWindow_entail_wit_1_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_4
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro idx hidx
  omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 : maxSlidingWindow_entail_wit_1_split_goal_5 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_5
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact ⟨PreH1, by omega, by omega, rfl⟩

-- Keep the generated residual branch and real SL preprocessing. Goal_apply
-- needs explicit arguments and pure-context extraction; forall conclusions
-- additionally use direct application when its parameter matcher cannot close them.
theorem proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1 := by
  unfold maxSlidingWindow_entail_wit_1
  right
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 : maxSlidingWindow_entail_wit_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_2_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 : maxSlidingWindow_entail_wit_2_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_2_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  refine ⟨PreH21.1, PreH21.2.1, PreH21.2.2.1, ?_⟩
  intro idx hidx hw
  exact PreH21.2.2.2.1 idx hidx (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2 := by
  unfold maxSlidingWindow_entail_wit_2
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 : maxSlidingWindow_entail_wit_3_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_3_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact drop_loop_remove_expired_head__head_drop_transitions l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 : maxSlidingWindow_entail_wit_3_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_3_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rcases PreH20 with ⟨hlen, hp, hb, ht, he⟩
  refine ⟨hlen, hp, by omega, ht, ?_⟩
  intro pos hpos
  exact he pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3 := by
  unfold maxSlidingWindow_entail_wit_3
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 : maxSlidingWindow_entail_wit_4_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_4_1_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 : maxSlidingWindow_entail_wit_4_1_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_4_1_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  refine ⟨?_, PreH20.2.1, PreH20.2.2.1, PreH20.2.2.2⟩
  intro pos hpos
  omega

theorem proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1 := by
  unfold maxSlidingWindow_entail_wit_4_1
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 : maxSlidingWindow_entail_wit_4_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_4_2_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 : maxSlidingWindow_entail_wit_4_2_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_4_2_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact drop_loop_exit_nonexpired__head_drop_transitions l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2 := by
  unfold maxSlidingWindow_entail_wit_4_2
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 : maxSlidingWindow_entail_wit_5_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH20

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 : maxSlidingWindow_entail_wit_5_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  refine ⟨PreH19.1, PreH19.2.1, PreH19.2.2.1, ?_⟩
  intro idx hidx hw
  exact Or.inl (PreH19.2.2.2 idx hidx hw)

theorem proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5 := by
  unfold maxSlidingWindow_entail_wit_5
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 : maxSlidingWindow_entail_wit_6_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_6_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact SWMQueuePendingState_drop_tail__pending_and_tail_drop l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 : maxSlidingWindow_entail_wit_6_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_6_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rcases PreH20 with ⟨hlen, hp, hb, ht, he⟩
  refine ⟨hlen, hp, by omega, by omega, ?_⟩
  intro pos hpos
  exact he pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6 := by
  unfold maxSlidingWindow_entail_wit_6
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)

theorem proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 : maxSlidingWindow_entail_wit_7_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_7_1_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1 := by
  unfold maxSlidingWindow_entail_wit_7_1
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 : maxSlidingWindow_entail_wit_7_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_7_2_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2 := by
  unfold maxSlidingWindow_entail_wit_7_2
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 : maxSlidingWindow_entail_wit_8_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact replace_Znth_append_bounds__value_loop_exit_and_append q_l_2 head tail i n_pre
    PreH5 ⟨PreH8, PreH9⟩ ⟨PreH10, PreH7⟩ PreH20

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 : maxSlidingWindow_entail_wit_8_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact queue_append_state__value_loop_exit_and_append l q_l_2 head tail i k_pre
    (by omega) PreH1 (by omega) ⟨PreH8, PreH9⟩ PreH10 PreH19 PreH22

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 : maxSlidingWindow_entail_wit_8_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_3
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply queue_append_storage__value_loop_exit_and_append l q_l_2 head tail i
  · omega
  · omega
  · exact ⟨PreH8, PreH9⟩
  · exact PreH10
  · intro pos hp
    rw [PreH4]
    exact PreH20 pos hp

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 : maxSlidingWindow_entail_wit_8_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_4
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [Zlength_replace_Znth]; exact PreH5

theorem proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8 := by
  unfold maxSlidingWindow_entail_wit_8
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 : maxSlidingWindow_entail_wit_9_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h := PreH20.2.2.2.2 (show head < tail ∧ k_pre ≤ i+1 by omega)
  rw [show i-k_pre+1 = i+1-k_pre by omega]
  exact h

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 : maxSlidingWindow_entail_wit_9_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9 := by
  unfold maxSlidingWindow_entail_wit_9
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 : maxSlidingWindow_entail_wit_10_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_10_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 : maxSlidingWindow_entail_wit_10_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_10_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rw [← PreH14]
  apply SWMOutputPrefix_app_single__window_output_append l k_pre out_idx out_l_2 _ PreH18 PreH19
  rw [PreH14, show i-k_pre+1+k_pre = i+1 by omega]
  exact PreH23

theorem proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 : maxSlidingWindow_entail_wit_10_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_10_split_goal_3
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rw [← PreH14]
  apply SWMOutputPrefixShape_app_single__window_output_append l k_pre out_idx out_l_2 _ PreH18
  omega

theorem proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10 := by
  unfold maxSlidingWindow_entail_wit_10
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)

theorem proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 : maxSlidingWindow_entail_wit_11_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_11_1_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH19

theorem proof_of_maxSlidingWindow_entail_wit_11_1 : maxSlidingWindow_entail_wit_11_1 := by
  unfold maxSlidingWindow_entail_wit_11_1
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | exact (proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 : maxSlidingWindow_entail_wit_11_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_11_2_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_11_2 : maxSlidingWindow_entail_wit_11_2 := by
  unfold maxSlidingWindow_entail_wit_11_2
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 : maxSlidingWindow_entail_wit_12_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_12_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12 := by
  unfold maxSlidingWindow_entail_wit_12
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13 := by
  unfold maxSlidingWindow_entail_wit_13
  right
  intro out_pre k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hi : i = n_pre := by omega
  have ho : out_idx = n_pre-k_pre+1 := by have := PreH15 (by omega); omega
  have hresult : SlidingWindowMaximum l k_pre out_l_2 := by
    have hlen := PreH18.2.2.2
    refine ⟨by omega, ?_⟩
    intro idx hidx
    exact PreH19 idx (by omega)
  rw [ho]
  Exists out_l_2
  split_pure_spatial
  · sep_apply (naive_C_Rules.IntArray.seg_to_full out_pre 0 (n_pre-k_pre+1) out_l_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

end SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_proof_manual
