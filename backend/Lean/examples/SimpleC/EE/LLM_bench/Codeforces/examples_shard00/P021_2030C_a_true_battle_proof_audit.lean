import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_proof_manual

run_cmd do
  let proved := #[
    ``no_adjacent_ones_before_succ__loop_transition,
    ``spec_zero_from_completed_scan__final_results,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1_split_goal_3,
    ``proof_of_solver_entail_wit_1_split_goal_4,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_1_split_goal_1,
    ``proof_of_solver_entail_wit_2_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_1,
    ``proof_of_solver_entail_wit_2_2,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2_split_goal_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3_split_goal_1,
    ``proof_of_solver_return_wit_3,
    ``proof_of_solver_return_wit_4_split_goal_1,
    ``proof_of_solver_return_wit_4]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
