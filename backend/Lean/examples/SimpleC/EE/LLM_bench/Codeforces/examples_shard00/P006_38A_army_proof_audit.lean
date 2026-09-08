import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal_check

-- All 13 source Qed declarations: one library lemma and twelve manual proofs.
run_cmd do
  let completed : List Lean.Name := [
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib.Spec_succ__loop_step,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_safety_wit_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_safety_wit_3_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_safety_wit_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_2_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_2_split_goal_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_return_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual.proof_of_solver_return_wit_1
  ]
  for decl in completed do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed proof {decl} depends on sorryAx"
  Lean.logInfo "Checked all 13 source Qed declarations: no recursive sorryAx dependencies."
