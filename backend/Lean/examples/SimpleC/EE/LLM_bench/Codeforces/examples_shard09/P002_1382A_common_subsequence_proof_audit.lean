import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_goal_check

-- All 16 source manual Qed declarations, including the ten split-goal helpers.
-- Recursive checking covers both private subsequence helper lemmas as well.
run_cmd do
  let completed : List Lean.Name := [
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_1_split_goal_spatial,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4_split_goal_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4_split_goal_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4_split_goal_5,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4_split_goal_6,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_entail_wit_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_return_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual.proof_of_solver_return_wit_2
  ]
  for decl in completed do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed proof {decl} depends on sorryAx"
  Lean.logInfo "Checked all 16 source manual Qed declarations: no recursive sorryAx dependencies."
