import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_goal_check

run_cmd do
  let proved := #[``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.scan_state_step_zero__scan_state_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.scan_state_step_new_run__scan_state_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.scan_state_step_inside_run__scan_state_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.Znth_repeat_exact__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.Forall_zero_Znth__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.pointwise_zero_eq_repeat__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.Forall_zero_repeat__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.nonzero_has_start__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.zero_then_nonzero_has_later_start__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.segment_mex_zero__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.segment_mex_exists__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.prefix_zero_all__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.prefix_one_run_shape__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.prefix_two_starts__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.zero_trace__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.one_trace__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.two_trace__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.trace_cost_ge_one__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.onesnap_two_starts_impossible__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.trace_cost_ge_two__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib.scan_state_complete_spec__final_spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_2_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_2_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_2_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_entail_wit_2_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_return_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_return_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_return_wit_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual.proof_of_solver_return_wit_2]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "source Qed depends on sorryAx: {decl}"
  Lean.logInfo "Verified 34 source Qed declarations without sorryAx"
