import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_proof_manual

-- Audit the 4 source library Qed and 25 source manual Qed independently of
-- the 9 inherited auto Admitted declarations.
run_cmd do
  let proved := #[
    ``numeral_sublist_succ__numeral_arithmetic,
    ``pow40_successor_bound__numeral_arithmetic,
    ``pow40_int64_bound__numeral_arithmetic,
    ``numeral_sublist_full__numeral_endpoints,
    ``proof_of_numeral_value_safety_wit_4_split_goal_1,
    ``proof_of_numeral_value_safety_wit_4_split_goal_2,
    ``proof_of_numeral_value_safety_wit_4,
    ``proof_of_numeral_value_safety_wit_5_split_goal_1,
    ``proof_of_numeral_value_safety_wit_5_split_goal_2,
    ``proof_of_numeral_value_safety_wit_5,
    ``proof_of_numeral_value_entail_wit_1_split_goal_1,
    ``proof_of_numeral_value_entail_wit_1_split_goal_2,
    ``proof_of_numeral_value_entail_wit_1_split_goal_3,
    ``proof_of_numeral_value_entail_wit_1,
    ``proof_of_numeral_value_entail_wit_2_split_goal_1,
    ``proof_of_numeral_value_entail_wit_2_split_goal_2,
    ``proof_of_numeral_value_entail_wit_2,
    ``proof_of_numeral_value_return_wit_1_split_goal_1,
    ``proof_of_numeral_value_return_wit_1,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2_split_goal_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3_split_goal_1,
    ``proof_of_solver_return_wit_3,
    ``proof_of_solver_partial_solve_wit_1_pure_split_goal_1,
    ``proof_of_solver_partial_solve_wit_1_pure,
    ``proof_of_solver_partial_solve_wit_2_pure_split_goal_1,
    ``proof_of_solver_partial_solve_wit_2_pure]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
