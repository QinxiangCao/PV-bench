import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_proof_manual

-- All six source manual Qed proofs, including the three public split-goal helpers,
-- must remain independent of the four inherited auto Admitted declarations.
run_cmd do
  let proved := #[
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_split_goal_1,
    ``proof_of_solver_entail_wit_2,
    ``proof_of_solver_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
