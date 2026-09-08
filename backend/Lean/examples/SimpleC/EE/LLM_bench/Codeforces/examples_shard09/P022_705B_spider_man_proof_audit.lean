import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_goal_check
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_proof_manual

run_cmd do
  let proved := #[
    ``land_one_eq_rem_two_nonnegative__parity_foundation,
    ``forall_Znth_intro__prefix_evolution,
    ``cycle_move_count_nonnegative__prefix_evolution,
    ``cycle_move_count_sublist_succ__prefix_evolution,
    ``spider_prefix_state_extend__prefix_evolution,
    ``permutation_sum__final_result,
    ``permutation_Zlength__final_result,
    ``fold_add_app__final_result,
    ``split_move_count_step__final_result,
    ``Forall_firstn__final_result,
    ``Forall_skipn__final_result,
    ``Forall_sublist__final_result,
    ``split_move_positive__final_result,
    ``cycle_count_ones__final_result,
    ``cycle_count_nonnegative__final_result,
    ``cycle_count_zero_ones__final_result,
    ``decrement_telescope__final_result,
    ``split_play_move_count__final_result,
    ``In_Znth_Zlength__final_result,
    ``split_move_exists__final_result,
    ``positive_cycle_nonterminal__final_result,
    ``extend_history_first__final_result,
    ``extend_history_last__final_result,
    ``extend_history_steps__final_result,
    ``extend_history_nonterminal__final_result,
    ``extend_history_follows__final_result,
    ``strategy_play_exists_from_history__final_result,
    ``even_successor_iff_odd__final_result,
    ``strategy_play_exists__final_result,
    ``split_first_wins_iff_odd__final_result,
    ``spider_prefix_state_implies_spec__final_result,
    ``proof_of_next_parity_return_wit_1_split_goal_1,
    ``proof_of_next_parity_return_wit_1,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1_split_goal_spatial,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_1_split_goal_1,
    ``proof_of_solver_entail_wit_2_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_1,
    ``proof_of_solver_entail_wit_2_2,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_partial_solve_wit_2_pure_split_goal_1,
    ``proof_of_solver_partial_solve_wit_2_pure_split_goal_2,
    ``proof_of_solver_partial_solve_wit_2_pure
  ]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P022 spider: all 45 source Qed recursively audited without sorryAx"
