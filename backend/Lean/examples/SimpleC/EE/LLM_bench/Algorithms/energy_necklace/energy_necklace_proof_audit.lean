import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal_check

open SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
open SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_proof_manual

-- All 23 library Qed and 33 manual Qed retain their Coq public names.
-- The 59 source auto Admitted are inherited separately.
run_cmd do
  let proved := #[
    ``EnergyValsDuplicated_label_bound__arithmetic_safety_bounds,
    ``EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds,
    ``EnergyIntervalBest_single_zero__prefix_table_bootstrap,
    ``EnergyZeroTable_len_done_2__prefix_table_bootstrap,
    ``EnergyZeroTable_from_prefix__prefix_table_bootstrap,
    ``EnergySplitCandidate_ext_eq__dp_interval_progress,
    ``EnergySplitProgress_step_keep__dp_interval_progress,
    ``EnergySplitProgress_step_take__dp_interval_progress,
    ``EnergySplitCandidate_plan__dp_interval_progress,
    ``EnergySplitProgress_finish_interval_best__dp_interval_progress,
    ``EnergyCellIndex_inj__dp_interval_progress,
    ``EnergyLenDone_replace_current__dp_interval_progress,
    ``EnergyLeftProgress_step_update__dp_interval_progress,
    ``EnergyLeftProgress_finish_len__dp_interval_progress,
    ``EnergyAnswerProgress_answer_bounds__answer_loop,
    ``EnergyLenDone_to_answer_len__answer_loop,
    ``EnergyLenDone_rotation_cell_best__answer_loop,
    ``EnergyAnswerCellBounded__answer_loop,
    ``EnergyIntervalBest_unique__answer_loop,
    ``EnergyValsDuplicated_unique__answer_loop,
    ``EnergyAnswerProgress_step_keep__answer_loop,
    ``EnergyAnswerProgress_step_update__answer_loop,
    ``EnergyAnswerProgress_finish__answer_loop,
    ``proof_of_energyNecklace_safety_wit_25,
    ``proof_of_energyNecklace_safety_wit_27,
    ``proof_of_energyNecklace_safety_wit_31,
    ``proof_of_energyNecklace_safety_wit_32,
    ``proof_of_energyNecklace_entail_wit_2,
    ``proof_of_energyNecklace_entail_wit_3,
    ``proof_of_energyNecklace_entail_wit_4,
    ``proof_of_energyNecklace_entail_wit_5,
    ``proof_of_energyNecklace_entail_wit_6,
    ``proof_of_energyNecklace_entail_wit_7,
    ``proof_of_energyNecklace_entail_wit_8,
    ``proof_of_energyNecklace_entail_wit_9,
    ``proof_of_energyNecklace_entail_wit_10,
    ``proof_of_energyNecklace_entail_wit_12,
    ``proof_of_energyNecklace_entail_wit_13,
    ``proof_of_energyNecklace_entail_wit_14,
    ``proof_of_energyNecklace_entail_wit_15,
    ``proof_of_energyNecklace_entail_wit_16,
    ``proof_of_energyNecklace_entail_wit_17_2,
    ``proof_of_energyNecklace_entail_wit_17_1,
    ``proof_of_energyNecklace_entail_wit_19,
    ``proof_of_energyNecklace_entail_wit_20,
    ``proof_of_energyNecklace_entail_wit_22,
    ``proof_of_energyNecklace_entail_wit_24,
    ``proof_of_energyNecklace_entail_wit_25,
    ``proof_of_energyNecklace_entail_wit_26_split_goal_1,
    ``proof_of_energyNecklace_entail_wit_26_split_goal_2,
    ``proof_of_energyNecklace_entail_wit_26,
    ``proof_of_energyNecklace_entail_wit_27,
    ``proof_of_energyNecklace_entail_wit_28_2,
    ``proof_of_energyNecklace_entail_wit_28_1,
    ``proof_of_energyNecklace_entail_wit_30,
    ``proof_of_energyNecklace_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed energy_necklace proof {decl} depends on sorryAx"
