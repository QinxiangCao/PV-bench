import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_proof_manual

run_cmd do
  let proved := #[
    ``Zlength_concat_uniform__initialization,
    ``Znth_In_range__results,
    ``In_Znth_Zlength__results,
    ``pre_rectangular_facts__initialization,
    ``has_color_concat_characterization__results,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1_split_goal_3,
    ``proof_of_solver_entail_wit_1_split_goal_4,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3,
    ``proof_of_solver_return_wit_4]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
