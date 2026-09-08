import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_proof_manual

run_cmd do
  let proved := #[
    ``DeletePair_snoc__stack_transitions,
    ``no_DeletePair_snoc__stack_transitions,
    ``no_DeletePair_prefix__stack_transitions,
    ``DeletePair_last_equal__stack_transitions,
    ``Zlength_map__stack_transitions,
    ``Znth_map__stack_transitions,
    ``Spec_extend_keep_distinct__stack_transitions,
    ``Spec_extend_drop_equal__stack_transitions,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1_split_goal_3,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_2,
    ``proof_of_solver_entail_wit_2_2,
    ``proof_of_solver_entail_wit_2_3_split_goal_1,
    ``proof_of_solver_entail_wit_2_3_split_goal_2,
    ``proof_of_solver_entail_wit_2_3,
    ``proof_of_solver_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
