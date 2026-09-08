import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_proof_manual

run_cmd do
  let proved := #[
    ``lxor_u64_bound__bit_scan_transitions,
    ``highest_bit_scan_zero_step__bit_scan_transitions,
    ``land_shiftr_one_bit__interval_maximum,
    ``boundary_xor__interval_maximum,
    ``interval_max_xor_from_scan__interval_maximum,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1_split_goal_3,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_split_goal_1,
    ``proof_of_solver_entail_wit_2_split_goal_2,
    ``proof_of_solver_entail_wit_2,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2_split_goal_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3_split_goal_1,
    ``proof_of_solver_return_wit_3]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P055: all 18 source Qed checked recursively; no sorryAx dependency."
