import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_goal_check

run_cmd do
  let proved := #[``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.obfuscation_prefix_init__initialization,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.app_zero_nonzero_index_lt_length__prefix_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.obfuscation_prefix_step_equal_increment__prefix_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.obfuscation_prefix_step_below__prefix_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.obfuscation_prefix_step_max__prefix_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.app_zero_terminator_index_eq_length__final_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.obfuscation_prefix_success_spec__final_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib.obfuscation_prefix_failure_spec__final_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_3_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_entail_wit_2_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_return_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_return_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_return_wit_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual.proof_of_solver_return_wit_2]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "source Qed depends on sorryAx: {decl}"
  Lean.logInfo "Verified 24 source Qed declarations without sorryAx"
