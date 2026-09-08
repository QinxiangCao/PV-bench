import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_proof_manual

-- All 34 Coq manual Qed declarations, including the 19 split-goal helpers,
-- must remain independent of the 56 inherited auto Admitted declarations.
run_cmd do
  let proved := #[
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_3_split_goal_1,
    ``proof_of_solver_entail_wit_3_split_goal_2,
    ``proof_of_solver_entail_wit_3,
    ``proof_of_solver_entail_wit_4_split_goal_1,
    ``proof_of_solver_entail_wit_4_split_goal_2,
    ``proof_of_solver_entail_wit_4_split_goal_3,
    ``proof_of_solver_entail_wit_4,
    ``proof_of_solver_entail_wit_5_1_split_goal_1,
    ``proof_of_solver_entail_wit_5_1,
    ``proof_of_solver_entail_wit_5_3_split_goal_1,
    ``proof_of_solver_entail_wit_5_3,
    ``proof_of_solver_entail_wit_5_4_split_goal_1,
    ``proof_of_solver_entail_wit_5_4,
    ``proof_of_solver_entail_wit_5_5_split_goal_1,
    ``proof_of_solver_entail_wit_5_5,
    ``proof_of_solver_entail_wit_6_split_goal_1,
    ``proof_of_solver_entail_wit_6_split_goal_2,
    ``proof_of_solver_entail_wit_6,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2_split_goal_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3_split_goal_1,
    ``proof_of_solver_return_wit_3,
    ``proof_of_solver_return_wit_4_split_goal_1,
    ``proof_of_solver_return_wit_4,
    ``proof_of_solver_return_wit_5_split_goal_1,
    ``proof_of_solver_return_wit_5,
    ``proof_of_solver_return_wit_6_split_goal_1,
    ``proof_of_solver_return_wit_6,
    ``proof_of_solver_return_wit_7_split_goal_1,
    ``proof_of_solver_return_wit_7]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
