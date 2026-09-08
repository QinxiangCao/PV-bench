import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_proof_manual

run_cmd do
  let proved := #[
    ``dominant_purchase_empty__initialization,
    ``sublist_step__backward_transitions,
    ``feasible_purchase_cons__backward_transitions,
    ``feasible_purchase_tail__backward_transitions,
    ``dominant_purchase_cons__backward_transitions,
    ``suffix_dominant_prepend__backward_transitions,
    ``fold_right_Z_add_le__final_result,
    ``suffix_dominant_state_to_spec__final_result,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_1_split_goal_1,
    ``proof_of_solver_entail_wit_2_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_1,
    ``proof_of_solver_entail_wit_2_2,
    ``proof_of_solver_entail_wit_2_3_split_goal_1,
    ``proof_of_solver_entail_wit_2_3,
    ``proof_of_solver_entail_wit_2_4_split_goal_1,
    ``proof_of_solver_entail_wit_2_4,
    ``proof_of_solver_entail_wit_2_5_split_goal_1,
    ``proof_of_solver_entail_wit_2_5,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P012 chocolates: all 23 source Qed checked recursively; no sorryAx dependency."
