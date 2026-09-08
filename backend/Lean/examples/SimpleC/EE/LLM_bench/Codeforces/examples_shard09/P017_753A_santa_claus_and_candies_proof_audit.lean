import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_proof_manual

run_cmd do
  let proved := #[
    ``candy_prefix_last_value__arithmetic_and_prefix,
    ``candy_prefix_snoc__arithmetic_and_prefix,
    ``triangular_succ__greedy_finalization,
    ``triangular_monotone_nonneg__greedy_finalization,
    ``sum_range_succ__greedy_finalization,
    ``candy_prefix_sum__greedy_finalization,
    ``sum_replace_Znth__greedy_finalization,
    ``sum_permutation__greedy_finalization,
    ``sorted_distinct_sum_lower_general__greedy_finalization,
    ``distinct_positive_sum_lower__greedy_finalization,
    ``greedy_candy_plan_spec__greedy_finalization,
    ``proof_of_solver_safety_wit_14_split_goal_1,
    ``proof_of_solver_safety_wit_14_split_goal_2,
    ``proof_of_solver_safety_wit_14,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_split_goal_1,
    ``proof_of_solver_entail_wit_2,
    ``proof_of_solver_entail_wit_3_split_goal_1,
    ``proof_of_solver_entail_wit_3_split_goal_2,
    ``proof_of_solver_entail_wit_3,
    ``proof_of_solver_entail_wit_4_split_goal_1,
    ``proof_of_solver_entail_wit_4,
    ``proof_of_solver_entail_wit_5,
    ``proof_of_solver_return_wit_1,
    ``integer_range_sum_empty,
    ``integer_range_sum_succ]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed or interval bridge {decl} depends on sorryAx"
  Lean.logInfo "P017 candies: all 25 source Qed and both integer interval equations checked recursively; no sorryAx dependency."
