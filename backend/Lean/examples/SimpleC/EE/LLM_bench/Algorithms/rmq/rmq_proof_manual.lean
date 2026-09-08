import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_goal
import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open rmq_goal rmq_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_build_safety_wit_2_split_goal_1 : build_safety_wit_2_split_goal_1 := by
  unfold build_safety_wit_2_split_goal_1
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_2_split_goal_2 : build_safety_wit_2_split_goal_2 := by
  unfold build_safety_wit_2_split_goal_2
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_4_split_goal_1 : build_safety_wit_4_split_goal_1 := by
  unfold build_safety_wit_4_split_goal_1
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_4_split_goal_2 : build_safety_wit_4_split_goal_2 := by
  unfold build_safety_wit_4_split_goal_2
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_6_split_goal_1 : build_safety_wit_6_split_goal_1 := by
  unfold build_safety_wit_6_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_6_split_goal_2 : build_safety_wit_6_split_goal_2 := by
  unfold build_safety_wit_6_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_12_split_goal_1 : build_safety_wit_12_split_goal_1 := by
  unfold build_safety_wit_12_split_goal_1
  intro st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_12_split_goal_2 : build_safety_wit_12_split_goal_2 := by
  unfold build_safety_wit_12_split_goal_2
  intro st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_13_split_goal_1 : build_safety_wit_13_split_goal_1 := by
  unfold build_safety_wit_13_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_13_split_goal_2 : build_safety_wit_13_split_goal_2 := by
  unfold build_safety_wit_13_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_14_split_goal_1 : build_safety_wit_14_split_goal_1 := by
  unfold build_safety_wit_14_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_14_split_goal_2 : build_safety_wit_14_split_goal_2 := by
  unfold build_safety_wit_14_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_15_split_goal_1 : build_safety_wit_15_split_goal_1 := by
  unfold build_safety_wit_15_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_15_split_goal_2 : build_safety_wit_15_split_goal_2 := by
  unfold build_safety_wit_15_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_17_split_goal_1 : build_safety_wit_17_split_goal_1 := by
  unfold build_safety_wit_17_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_17_split_goal_2 : build_safety_wit_17_split_goal_2 := by
  unfold build_safety_wit_17_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_18_split_goal_1 : build_safety_wit_18_split_goal_1 := by
  unfold build_safety_wit_18_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_18_split_goal_2 : build_safety_wit_18_split_goal_2 := by
  unfold build_safety_wit_18_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_19_split_goal_1 : build_safety_wit_19_split_goal_1 := by
  unfold build_safety_wit_19_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_19_split_goal_2 : build_safety_wit_19_split_goal_2 := by
  unfold build_safety_wit_19_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_20_split_goal_1 : build_safety_wit_20_split_goal_1 := by
  unfold build_safety_wit_20_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_20_split_goal_2 : build_safety_wit_20_split_goal_2 := by
  unfold build_safety_wit_20_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_22_split_goal_1 : build_safety_wit_22_split_goal_1 := by
  unfold build_safety_wit_22_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_22_split_goal_2 : build_safety_wit_22_split_goal_2 := by
  unfold build_safety_wit_22_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_23_split_goal_1 : build_safety_wit_23_split_goal_1 := by
  unfold build_safety_wit_23_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_23_split_goal_2 : build_safety_wit_23_split_goal_2 := by
  unfold build_safety_wit_23_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_24_split_goal_1 : build_safety_wit_24_split_goal_1 := by
  unfold build_safety_wit_24_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_24_split_goal_2 : build_safety_wit_24_split_goal_2 := by
  unfold build_safety_wit_24_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_25_split_goal_1 : build_safety_wit_25_split_goal_1 := by
  unfold build_safety_wit_25_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_25_split_goal_2 : build_safety_wit_25_split_goal_2 := by
  unfold build_safety_wit_25_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_26_split_goal_1 : build_safety_wit_26_split_goal_1 := by
  unfold build_safety_wit_26_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_26_split_goal_2 : build_safety_wit_26_split_goal_2 := by
  unfold build_safety_wit_26_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_27_split_goal_1 : build_safety_wit_27_split_goal_1 := by
  unfold build_safety_wit_27_split_goal_1
  intro st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_safety_wit_27_split_goal_2 : build_safety_wit_27_split_goal_2 := by
  unfold build_safety_wit_27_split_goal_2
  intro st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hpn := worker_Power2_nonneg j
  have hhn := worker_Power2_nonneg (j-1)
  try have hdouble := Power2_sub1_double j (by omega)
  try have hpb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_1_split_goal_1 : build_entail_wit_1_split_goal_1 := by
  unfold build_entail_wit_1_split_goal_1
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  intro p hp
  omega

theorem proof_of_build_entail_wit_1_split_goal_2 : build_entail_wit_1_split_goal_2 := by
  unfold build_entail_wit_1_split_goal_2
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  exact ⟨le_refl _,Zlength_nonneg st0⟩

theorem proof_of_build_entail_wit_1_split_goal_3 : build_entail_wit_1_split_goal_3 := by
  unfold build_entail_wit_1_split_goal_3
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_2_split_goal_1 : build_entail_wit_2_split_goal_1 := by
  unfold build_entail_wit_2_split_goal_1
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply STZeroPrefix_replace_zero_step st_l_2 idx PreH8
  omega

theorem proof_of_build_entail_wit_2_split_goal_2 : build_entail_wit_2_split_goal_2 := by
  unfold build_entail_wit_2_split_goal_2
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_2_split_goal_3 : build_entail_wit_2_split_goal_3 := by
  unfold build_entail_wit_2_split_goal_3
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1 := by
  unfold build_entail_wit_3_split_goal_1
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : idx = n_pre*K_pre := by omega
  exact he ▸ PreH8

theorem proof_of_build_entail_wit_3_split_goal_2 : build_entail_wit_3_split_goal_2 := by
  unfold build_entail_wit_3_split_goal_2
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : idx = n_pre*K_pre := by omega
  exact he ▸ PreH7

theorem proof_of_build_entail_wit_4_split_goal_1 : build_entail_wit_4_split_goal_1 := by
  unfold build_entail_wit_4_split_goal_1
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  intro i hi
  omega

theorem proof_of_build_entail_wit_4_split_goal_2 : build_entail_wit_4_split_goal_2 := by
  unfold build_entail_wit_4_split_goal_2
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_1 : build_entail_wit_5_split_goal_1 := by
  unfold build_entail_wit_5_split_goal_1
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_2 : build_entail_wit_5_split_goal_2 := by
  unfold build_entail_wit_5_split_goal_2
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_3 : build_entail_wit_5_split_goal_3 := by
  unfold build_entail_wit_5_split_goal_3
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_5_split_goal_4 : build_entail_wit_5_split_goal_4 := by
  unfold build_entail_wit_5_split_goal_4
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_6_split_goal_1 : build_entail_wit_6_split_goal_1 := by
  unfold build_entail_wit_6_split_goal_1
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply worker_STBasePrefix_write_base_step l st_l_2 K_pre n_pre i <;> first | assumption | omega | nlinarith

theorem proof_of_build_entail_wit_6_split_goal_2 : build_entail_wit_6_split_goal_2 := by
  unfold build_entail_wit_6_split_goal_2
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_6_split_goal_3 : build_entail_wit_6_split_goal_3 := by
  unfold build_entail_wit_6_split_goal_3
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_8_split_goal_1 : build_entail_wit_8_split_goal_1 := by
  unfold build_entail_wit_8_split_goal_1
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply worker_STBasePrefix_complete_level1 l st_l_2 K_pre n_pre i <;> first | assumption | omega

theorem proof_of_build_entail_wit_8_split_goal_2 : build_entail_wit_8_split_goal_2 := by
  unfold build_entail_wit_8_split_goal_2
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_9_split_goal_1 : build_entail_wit_9_split_goal_1 := by
  unfold build_entail_wit_9_split_goal_1
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  rfl

theorem proof_of_build_entail_wit_9_split_goal_2 : build_entail_wit_9_split_goal_2 := by
  unfold build_entail_wit_9_split_goal_2
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  rfl

theorem proof_of_build_entail_wit_9_split_goal_3 : build_entail_wit_9_split_goal_3 := by
  unfold build_entail_wit_9_split_goal_3
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_10_split_goal_1 : build_entail_wit_10_split_goal_1 := by
  unfold build_entail_wit_10_split_goal_1
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro i hi
  omega

theorem proof_of_build_entail_wit_10_split_goal_2 : build_entail_wit_10_split_goal_2 := by
  unfold build_entail_wit_10_split_goal_2
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_11_split_goal_1 : build_entail_wit_11_split_goal_1 := by
  unfold build_entail_wit_11_split_goal_1
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  apply PreH11
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_2 : build_entail_wit_11_split_goal_2 := by
  unfold build_entail_wit_11_split_goal_2
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  apply PreH11
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_3 : build_entail_wit_11_split_goal_3 := by
  unfold build_entail_wit_11_split_goal_3
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_4 : build_entail_wit_11_split_goal_4 := by
  unfold build_entail_wit_11_split_goal_4
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_5 : build_entail_wit_11_split_goal_5 := by
  unfold build_entail_wit_11_split_goal_5
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_6 : build_entail_wit_11_split_goal_6 := by
  unfold build_entail_wit_11_split_goal_6
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_7 : build_entail_wit_11_split_goal_7 := by
  unfold build_entail_wit_11_split_goal_7
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_8 : build_entail_wit_11_split_goal_8 := by
  unfold build_entail_wit_11_split_goal_8
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_9 : build_entail_wit_11_split_goal_9 := by
  unfold build_entail_wit_11_split_goal_9
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_10 : build_entail_wit_11_split_goal_10 := by
  unfold build_entail_wit_11_split_goal_10
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_11 : build_entail_wit_11_split_goal_11 := by
  unfold build_entail_wit_11_split_goal_11
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_11_split_goal_12 : build_entail_wit_11_split_goal_12 := by
  unfold build_entail_wit_11_split_goal_12
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_13_1_split_goal_1 : build_entail_wit_13_1_split_goal_1 := by
  unfold build_entail_wit_13_1_split_goal_1
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STLevelPrefix_extend_by_left_max l st_l_2 K_pre n_pre j i half a b
  all_goals first | assumption | omega | (simpa only [Int.add_sub_assoc] using PreH17) | (simpa only [Int.add_sub_assoc] using PreH18)

theorem proof_of_build_entail_wit_13_1_split_goal_2 : build_entail_wit_13_1_split_goal_2 := by
  unfold build_entail_wit_13_1_split_goal_2
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STBuiltBeforeLevel_replace_level_cell l st_l_2 K_pre n_pre j i
  · exact PreH24
  · exact PreH6
  · constructor <;> omega
  · intro row col hc
    have hp := Power2_pos col hc.2.1
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem proof_of_build_entail_wit_13_1_split_goal_3 : build_entail_wit_13_1_split_goal_3 := by
  unfold build_entail_wit_13_1_split_goal_3
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_13_1_split_goal_4 : build_entail_wit_13_1_split_goal_4 := by
  unfold build_entail_wit_13_1_split_goal_4
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) ((i+half)*K_pre+j-1) a ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH18

theorem proof_of_build_entail_wit_13_1_split_goal_5 : build_entail_wit_13_1_split_goal_5 := by
  unfold build_entail_wit_13_1_split_goal_5
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) (i*K_pre+j-1) a ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH17

theorem proof_of_build_entail_wit_13_1_split_goal_6 : build_entail_wit_13_1_split_goal_6 := by
  unfold build_entail_wit_13_1_split_goal_6
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Zlength_replace_Znth]
  exact PreH4

theorem proof_of_build_entail_wit_13_2_split_goal_1 : build_entail_wit_13_2_split_goal_1 := by
  unfold build_entail_wit_13_2_split_goal_1
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STLevelPrefix_extend_by_right_max l st_l_2 K_pre n_pre j i half a b
  all_goals first | assumption | omega | (simpa only [Int.add_sub_assoc] using PreH17) | (simpa only [Int.add_sub_assoc] using PreH18)

theorem proof_of_build_entail_wit_13_2_split_goal_2 : build_entail_wit_13_2_split_goal_2 := by
  unfold build_entail_wit_13_2_split_goal_2
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  apply STBuiltBeforeLevel_replace_level_cell l st_l_2 K_pre n_pre j i
  · exact PreH24
  · exact PreH6
  · constructor <;> omega
  · intro row col hc
    have hp := Power2_pos col hc.2.1
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem proof_of_build_entail_wit_13_2_split_goal_3 : build_entail_wit_13_2_split_goal_3 := by
  unfold build_entail_wit_13_2_split_goal_3
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  (repeat' constructor) <;> nlinarith

theorem proof_of_build_entail_wit_13_2_split_goal_4 : build_entail_wit_13_2_split_goal_4 := by
  unfold build_entail_wit_13_2_split_goal_4
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) ((i+half)*K_pre+j-1) b ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH18

theorem proof_of_build_entail_wit_13_2_split_goal_5 : build_entail_wit_13_2_split_goal_5 := by
  unfold build_entail_wit_13_2_split_goal_5
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Znth_replace_Znth_Diff 0 st_l_2 (i*K_pre+j) (i*K_pre+j-1) b ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by nlinarith)]
  exact PreH17

theorem proof_of_build_entail_wit_13_2_split_goal_6 : build_entail_wit_13_2_split_goal_6 := by
  unfold build_entail_wit_13_2_split_goal_6
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  rw [Zlength_replace_Znth]
  exact PreH4

theorem proof_of_build_entail_wit_15_split_goal_1 : build_entail_wit_15_split_goal_1 := by
  unfold build_entail_wit_15_split_goal_1
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  apply STLevelPrefix_exit_to_built_step l st_l_2 K_pre n_pre j i len <;> assumption

theorem proof_of_build_entail_wit_15_split_goal_2 : build_entail_wit_15_split_goal_2 := by
  unfold build_entail_wit_15_split_goal_2
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_build_entail_wit_16_split_goal_1 : build_entail_wit_16_split_goal_1 := by
  unfold build_entail_wit_16_split_goal_1
  intro K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [PreH7]
  exact Power2_step j (by omega)

theorem proof_of_build_entail_wit_16_split_goal_2 : build_entail_wit_16_split_goal_2 := by
  unfold build_entail_wit_16_split_goal_2
  intro K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  simpa only [show j+1-1 = j by omega] using PreH7

theorem proof_of_build_return_wit_1_split_goal_1 : build_return_wit_1_split_goal_1 := by
  unfold build_return_wit_1_split_goal_1
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : j = K_pre := by omega
  exact he ▸ PreH10

theorem proof_of_build_return_wit_1_split_goal_2 : build_return_wit_1_split_goal_2 := by
  unfold build_return_wit_1_split_goal_2
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : j = K_pre := by omega
  exact he ▸ PreH9

theorem proof_of_query_safety_wit_1_split_goal_1 : query_safety_wit_1_split_goal_1 := by
  unfold query_safety_wit_1_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_1_split_goal_2 : query_safety_wit_1_split_goal_2 := by
  unfold query_safety_wit_1_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_2_split_goal_1 : query_safety_wit_2_split_goal_1 := by
  unfold query_safety_wit_2_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_2_split_goal_2 : query_safety_wit_2_split_goal_2 := by
  unfold query_safety_wit_2_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_6_split_goal_1 : query_safety_wit_6_split_goal_1 := by
  unfold query_safety_wit_6_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_6_split_goal_2 : query_safety_wit_6_split_goal_2 := by
  unfold query_safety_wit_6_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_8_split_goal_1 : query_safety_wit_8_split_goal_1 := by
  unfold query_safety_wit_8_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_8_split_goal_2 : query_safety_wit_8_split_goal_2 := by
  unfold query_safety_wit_8_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_10_split_goal_1 : query_safety_wit_10_split_goal_1 := by
  unfold query_safety_wit_10_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_10_split_goal_2 : query_safety_wit_10_split_goal_2 := by
  unfold query_safety_wit_10_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_11_split_goal_1 : query_safety_wit_11_split_goal_1 := by
  unfold query_safety_wit_11_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_11_split_goal_2 : query_safety_wit_11_split_goal_2 := by
  unfold query_safety_wit_11_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_12_split_goal_1 : query_safety_wit_12_split_goal_1 := by
  unfold query_safety_wit_12_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_12_split_goal_2 : query_safety_wit_12_split_goal_2 := by
  unfold query_safety_wit_12_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_13_split_goal_1 : query_safety_wit_13_split_goal_1 := by
  unfold query_safety_wit_13_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_13_split_goal_2 : query_safety_wit_13_split_goal_2 := by
  unfold query_safety_wit_13_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_14_split_goal_1 : query_safety_wit_14_split_goal_1 := by
  unfold query_safety_wit_14_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_14_split_goal_2 : query_safety_wit_14_split_goal_2 := by
  unfold query_safety_wit_14_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_15_split_goal_1 : query_safety_wit_15_split_goal_1 := by
  unfold query_safety_wit_15_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_15_split_goal_2 : query_safety_wit_15_split_goal_2 := by
  unfold query_safety_wit_15_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_16_split_goal_1 : query_safety_wit_16_split_goal_1 := by
  unfold query_safety_wit_16_split_goal_1
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_safety_wit_16_split_goal_2 : query_safety_wit_16_split_goal_2 := by
  unfold query_safety_wit_16_split_goal_2
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try have hpb := worker_Power2_double_int_bound_30 k K_pre (by omega) (by omega)
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1 := by
  unfold query_entail_wit_1_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply QueryLogLoopState_init <;> omega

theorem proof_of_query_entail_wit_1_split_goal_2 : query_entail_wit_1_split_goal_2 := by
  unfold query_entail_wit_1_split_goal_2
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply QueryLogBounds_init <;> omega

theorem proof_of_query_entail_wit_2_split_goal_1 : query_entail_wit_2_split_goal_1 := by
  unfold query_entail_wit_2_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [← PreH4]
  apply QueryLogLoopState_step <;> assumption

theorem proof_of_query_entail_wit_2_split_goal_2 : query_entail_wit_2_split_goal_2 := by
  unfold query_entail_wit_2_split_goal_2
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [← PreH4]
  apply QueryLogBounds_step <;> assumption

theorem proof_of_query_entail_wit_3_split_goal_1 : query_entail_wit_3_split_goal_1 := by
  unfold query_entail_wit_3_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply PreH8
  (repeat' constructor) <;> omega

theorem proof_of_query_entail_wit_3_split_goal_2 : query_entail_wit_3_split_goal_2 := by
  unfold query_entail_wit_3_split_goal_2
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  apply PreH8
  (repeat' constructor) <;> omega

theorem proof_of_query_entail_wit_3_split_goal_3 : query_entail_wit_3_split_goal_3 := by
  unfold query_entail_wit_3_split_goal_3
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_4 : query_entail_wit_3_split_goal_4 := by
  unfold query_entail_wit_3_split_goal_4
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_5 : query_entail_wit_3_split_goal_5 := by
  unfold query_entail_wit_3_split_goal_5
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_6 : query_entail_wit_3_split_goal_6 := by
  unfold query_entail_wit_3_split_goal_6
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_7 : query_entail_wit_3_split_goal_7 := by
  unfold query_entail_wit_3_split_goal_7
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_8 : query_entail_wit_3_split_goal_8 := by
  unfold query_entail_wit_3_split_goal_8
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dsimp only [RMQSizeSafe,RMQInputValues,STTableShape,STCellBounds,STZeroPrefixBounds,STBasePrefixBounds,STBuiltBeforeLevelBounds,STLevelPrefixBounds,QueryIntervalBounds,QueryLogBounds,QueryLogFinalState,QueryLogLoopState] at *
  try rw [Zlength_replace_Znth]
  first | assumption | omega | ((repeat' constructor) <;> nlinarith)

theorem proof_of_query_entail_wit_3_split_goal_9 : query_entail_wit_3_split_goal_9 := by
  unfold query_entail_wit_3_split_goal_9
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [← PreH4]
  refine ⟨PreH10,?_⟩
  have hd := Power2_step_query k PreH10.1
  have hp := PreH10.2.1
  omega

theorem proof_of_query_entail_wit_5_split_goal_1 : query_entail_wit_5_split_goal_1 := by
  unfold query_entail_wit_5_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply RangeMaxValue_sparse_query_left l st_l K_pre n_pre len left_pre right_pre k pow a b <;> assumption

theorem proof_of_query_entail_wit_6_split_goal_1 : query_entail_wit_6_split_goal_1 := by
  unfold query_entail_wit_6_split_goal_1
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply RangeMaxValue_sparse_query_right l st_l K_pre n_pre len left_pre right_pre k pow a b <;> assumption

theorem proof_of_build_safety_wit_2 : build_safety_wit_2 := by
  unfold build_safety_wit_2
  right
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_2_split_goal_1 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    | exact (proof_of_build_safety_wit_2_split_goal_2 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)

theorem proof_of_build_safety_wit_4 : build_safety_wit_4 := by
  unfold build_safety_wit_4
  right
  intro st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_4_split_goal_1 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    | exact (proof_of_build_safety_wit_4_split_goal_2 st_pre K_pre n_pre arr_pre l idx st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_build_safety_wit_6 : build_safety_wit_6 := by
  unfold build_safety_wit_6
  right
  intro st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_6_split_goal_1 st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | exact (proof_of_build_safety_wit_6_split_goal_2 st_pre K_pre n_pre arr_pre l st_l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_build_safety_wit_12 : build_safety_wit_12 := by
  unfold build_safety_wit_12
  right
  intro st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_12_split_goal_1 st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | exact (proof_of_build_safety_wit_12_split_goal_2 st_pre K_pre n_pre arr_pre l i len half j st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

theorem proof_of_build_safety_wit_13 : build_safety_wit_13 := by
  unfold build_safety_wit_13
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_13_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_13_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_14 : build_safety_wit_14 := by
  unfold build_safety_wit_14
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_14_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_14_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_15 : build_safety_wit_15 := by
  unfold build_safety_wit_15
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_15_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_15_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_17 : build_safety_wit_17 := by
  unfold build_safety_wit_17
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_17_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_17_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_18 : build_safety_wit_18 := by
  unfold build_safety_wit_18
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_18_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_18_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_19 : build_safety_wit_19 := by
  unfold build_safety_wit_19
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_19_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_19_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_20 : build_safety_wit_20 := by
  unfold build_safety_wit_20
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_20_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)
    | exact (proof_of_build_safety_wit_20_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_build_safety_wit_22 : build_safety_wit_22 := by
  unfold build_safety_wit_22
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_22_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_22_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_23 : build_safety_wit_23 := by
  unfold build_safety_wit_23
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_23_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_23_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_24 : build_safety_wit_24 := by
  unfold build_safety_wit_24
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_24_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_24_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_25 : build_safety_wit_25 := by
  unfold build_safety_wit_25
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_25_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | exact (proof_of_build_safety_wit_25_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_safety_wit_26 : build_safety_wit_26 := by
  unfold build_safety_wit_26
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_26_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | exact (proof_of_build_safety_wit_26_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

theorem proof_of_build_safety_wit_27 : build_safety_wit_27 := by
  unfold build_safety_wit_27
  right
  intro st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact (proof_of_build_safety_wit_27_split_goal_1 st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_build_safety_wit_27_split_goal_2 st_pre K_pre n_pre arr_pre l st_l j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_build_entail_wit_1 : build_entail_wit_1 := by
  unfold build_entail_wit_1
  right
  intro K_pre n_pre st0 l PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_1_split_goal_1 K_pre n_pre st0 l PreH1 PreH2 PreH3)
      | exact (proof_of_build_entail_wit_1_split_goal_2 K_pre n_pre st0 l PreH1 PreH2 PreH3)
      | exact (proof_of_build_entail_wit_1_split_goal_3 K_pre n_pre st0 l PreH1 PreH2 PreH3)

theorem proof_of_build_entail_wit_2 : build_entail_wit_2 := by
  unfold build_entail_wit_2
  right
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_2_split_goal_1 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | exact (proof_of_build_entail_wit_2_split_goal_2 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | exact (proof_of_build_entail_wit_2_split_goal_3 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_build_entail_wit_3 : build_entail_wit_3 := by
  unfold build_entail_wit_3
  right
  intro K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_3_split_goal_1 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | exact (proof_of_build_entail_wit_3_split_goal_2 K_pre n_pre l idx st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)

theorem proof_of_build_entail_wit_4 : build_entail_wit_4 := by
  unfold build_entail_wit_4
  right
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_4_split_goal_1 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_build_entail_wit_4_split_goal_2 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)

theorem proof_of_build_entail_wit_5 : build_entail_wit_5 := by
  unfold build_entail_wit_5
  right
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_5_split_goal_1 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_5_split_goal_2 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_5_split_goal_3 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_5_split_goal_4 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_build_entail_wit_6 : build_entail_wit_6 := by
  unfold build_entail_wit_6
  right
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_6_split_goal_1 K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_entail_wit_6_split_goal_2 K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_entail_wit_6_split_goal_3 K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_build_entail_wit_8 : build_entail_wit_8 := by
  unfold build_entail_wit_8
  right
  intro K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_8_split_goal_1 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_build_entail_wit_8_split_goal_2 K_pre n_pre l i st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_build_entail_wit_9 : build_entail_wit_9 := by
  unfold build_entail_wit_9
  right
  intro K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_9_split_goal_1 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_build_entail_wit_9_split_goal_2 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)
      | exact (proof_of_build_entail_wit_9_split_goal_3 K_pre n_pre l st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5)

theorem proof_of_build_entail_wit_10 : build_entail_wit_10 := by
  unfold build_entail_wit_10
  right
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_10_split_goal_1 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_entail_wit_10_split_goal_2 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_build_entail_wit_11 : build_entail_wit_11 := by
  unfold build_entail_wit_11
  right
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_11_split_goal_1 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_2 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_3 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_4 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_5 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_6 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_7 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_8 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_9 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_10 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_11 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_11_split_goal_12 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_build_entail_wit_13_1 : build_entail_wit_13_1 := by
  unfold build_entail_wit_13_1
  right
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_13_1_split_goal_1 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_2 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_3 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_4 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_5 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_1_split_goal_6 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_entail_wit_13_2 : build_entail_wit_13_2 := by
  unfold build_entail_wit_13_2
  right
  intro K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_13_2_split_goal_1 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_2 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_3 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_4 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_5 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | exact (proof_of_build_entail_wit_13_2_split_goal_6 K_pre n_pre l st_l_2 j half len i a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)

theorem proof_of_build_entail_wit_15 : build_entail_wit_15 := by
  unfold build_entail_wit_15
  right
  intro K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_15_split_goal_1 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_build_entail_wit_15_split_goal_2 K_pre n_pre l i len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_build_entail_wit_16 : build_entail_wit_16 := by
  unfold build_entail_wit_16
  right
  intro K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_entail_wit_16_split_goal_1 K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
      | exact (proof_of_build_entail_wit_16_split_goal_2 K_pre n_pre l st_l_2 j half len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_build_return_wit_1 : build_return_wit_1 := by
  unfold build_return_wit_1
  right
  intro K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_build_return_wit_1_split_goal_1 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_build_return_wit_1_split_goal_2 K_pre n_pre l len half j st_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_safety_wit_1 : query_safety_wit_1 := by
  unfold query_safety_wit_1
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_1_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_query_safety_wit_1_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_query_safety_wit_2 : query_safety_wit_2 := by
  unfold query_safety_wit_2
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_2_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_query_safety_wit_2_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_query_safety_wit_6 : query_safety_wit_6 := by
  unfold query_safety_wit_6
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_6_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (proof_of_query_safety_wit_6_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_query_safety_wit_8 : query_safety_wit_8 := by
  unfold query_safety_wit_8
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_8_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | exact (proof_of_query_safety_wit_8_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_safety_wit_10 : query_safety_wit_10 := by
  unfold query_safety_wit_10
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_10_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
    | exact (proof_of_query_safety_wit_10_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_safety_wit_11 : query_safety_wit_11 := by
  unfold query_safety_wit_11
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_11_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_11_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_12 : query_safety_wit_12 := by
  unfold query_safety_wit_12
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_12_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_12_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_13 : query_safety_wit_13 := by
  unfold query_safety_wit_13
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_13_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_13_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_14 : query_safety_wit_14 := by
  unfold query_safety_wit_14
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_14_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_14_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_15 : query_safety_wit_15 := by
  unfold query_safety_wit_15
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_15_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_15_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_safety_wit_16 : query_safety_wit_16 := by
  unfold query_safety_wit_16
  right
  intro right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (proof_of_query_safety_wit_16_split_goal_1 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (proof_of_query_safety_wit_16_split_goal_2 right_pre left_pre K_pre n_pre st_pre st_l l len pow k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_query_entail_wit_1 : query_entail_wit_1 := by
  unfold query_entail_wit_1
  right
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_1_split_goal_1 right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | exact (proof_of_query_entail_wit_1_split_goal_2 right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_query_entail_wit_2 : query_entail_wit_2 := by
  unfold query_entail_wit_2
  right
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_2_split_goal_1 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_2_split_goal_2 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_entail_wit_3 : query_entail_wit_3 := by
  unfold query_entail_wit_3
  right
  intro right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_3_split_goal_1 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_2 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_3 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_4 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_5 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_6 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_7 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_8 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_query_entail_wit_3_split_goal_9 right_pre left_pre K_pre n_pre st_l l k pow len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_query_entail_wit_5 : query_entail_wit_5 := by
  unfold query_entail_wit_5
  right
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_5_split_goal_1 right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_query_entail_wit_6 : query_entail_wit_6 := by
  unfold query_entail_wit_6
  right
  intro right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_query_entail_wit_6_split_goal_1 right_pre left_pre K_pre n_pre st_l l len a k b pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

end SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_proof_manual
