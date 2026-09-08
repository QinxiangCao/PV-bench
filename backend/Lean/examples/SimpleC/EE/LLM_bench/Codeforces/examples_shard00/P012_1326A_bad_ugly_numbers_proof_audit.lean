import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_goal_check

run_cmd do
  let proved := #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.decimal_value_acc_last_digit_mod_2__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.decimal_value_last_digit_mod_2__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.decimal_value_acc_digit_sum_mod_3__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.decimal_value_digit_sum_mod_3__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.all_Znth_eq_Forall__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.fold_right_add_of_Forall_eq__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.decimal_fold_positive__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.last_of_Forall_eq__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.last_cons_nonempty__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.two_then_threes_bad_ugly__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.no_bad_ugly_length_one__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.Znth_map_inbounds_Z__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib.Zlength_map_Z__spec_results,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_proof_manual.proof_of_solver_entail_wit_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_proof_manual.proof_of_solver_entail_wit_2_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_proof_manual.proof_of_solver_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_proof_manual.proof_of_solver_return_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_proof_manual.proof_of_solver_return_wit_2
  ]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "CF00 P012: all 19 source Qed recursively audited without sorryAx"
