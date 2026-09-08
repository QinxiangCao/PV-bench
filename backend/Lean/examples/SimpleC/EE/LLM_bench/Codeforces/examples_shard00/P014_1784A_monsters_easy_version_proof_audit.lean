import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_goal_check

run_cmd do
  let proved := #[``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.Forall_Znth_bounds__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.Forall_Znth_elim__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.last_app_singleton__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.ZListSum_app__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.last_as_Znth__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.maximal_cascade_preparation_app_step__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.prefix_greedy_step__greedy_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_2_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_2_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_2_2_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_entail_wit_2_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_return_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual.proof_of_solver_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "source Qed depends on sorryAx: {decl}"
  Lean.logInfo "Verified 18 source Qed declarations without sorryAx"
