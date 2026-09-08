import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_goal_check

run_cmd do
  let proved := #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bitwise_scan_state_zero__scan_core,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bitwise_scan_state_succ__scan_core,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bounded_mask_1024__scan_core,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bounded_lor_land__scan_core,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bit_write_same__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bit_write_other__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.Zlength_replace_Znth__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.one_bit_swap_construct__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.one_bit_swap_occurs_iff__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.reachable_preserves_bit_counts__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.one_swap_reachable__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.force_bit_once__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.canonical_extrema_prefix__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bounded_testbit_high_false__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.canonical_extrema_reachable__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.land_le_nonnegative__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.In_Znth_index__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.reachable_elements_bounded_by_scan_extrema__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.array_spread_from_extrema_bounds__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib.bitwise_scan_final_implies_spec__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_2_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_2_split_goal_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_2_split_goal_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_2_split_goal_5,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_return_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual.proof_of_solver_return_wit_1
  ]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "CF00 P003: all 31 source Qed recursively audited without sorryAx"
