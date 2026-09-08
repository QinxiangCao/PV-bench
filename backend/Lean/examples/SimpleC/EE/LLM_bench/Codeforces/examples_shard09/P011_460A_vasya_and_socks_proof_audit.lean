import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_goal_check

-- All 11 source manual Qed declarations, including the seven split-goal helpers.
-- Recursive checking also covers their four private arithmetic helpers.
run_cmd do
  let completed : List Lean.Name := [
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_2_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_entail_wit_2_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_return_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual.proof_of_solver_return_wit_1
  ]
  for decl in completed do
    let axioms ← Lean.collectAxioms decl
    if axioms.contains ``sorryAx then
      throwError "Completed proof {decl} depends on sorryAx"
  Lean.logInfo "Checked all 11 source manual Qed declarations: no recursive sorryAx dependencies."
