import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_goal_check
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_proof_manual

run_cmd do
  let proved := #[
    ``perm4_acdb__final_results,
    ``perm4_cabd__final_results,
    ``perm4_dbac__final_results,
    ``perm4_bdca__final_results,
    ``perm4_bdac__final_results,
    ``perm4_badc__final_results,
    ``diagonal_abs_equal_of_corners__final_results,
    ``no_completion_of_nonaxis_unequal_abs_diffs__final_results,
    ``completes_square_diagonal__final_results,
    ``completes_square_horizontal__final_results,
    ``completes_square_vertical__final_results,
    ``proof_of_iabs_return_wit_1_split_goal_1,
    ``proof_of_iabs_return_wit_1,
    ``proof_of_iabs_return_wit_2_split_goal_1,
    ``proof_of_iabs_return_wit_2,
    ``proof_of_solver_safety_wit_3_split_goal_1,
    ``proof_of_solver_safety_wit_3_split_goal_2,
    ``proof_of_solver_safety_wit_3,
    ``proof_of_solver_safety_wit_12_split_goal_1,
    ``proof_of_solver_safety_wit_12_split_goal_2,
    ``proof_of_solver_safety_wit_12,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3,
    ``proof_of_solver_return_wit_4
  ]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P027 garden: all 26 source Qed recursively audited without sorryAx"
