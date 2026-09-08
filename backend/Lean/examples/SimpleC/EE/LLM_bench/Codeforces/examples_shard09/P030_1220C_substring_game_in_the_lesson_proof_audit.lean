import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_goal_check
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_proof_manual

run_cmd do
  let proved := #[
    ``Znth_app_left__prefix_transitions,
    ``Znth_app_last__prefix_transitions,
    ``prefix_minimum_step__prefix_transitions,
    ``spec_prefix_snoc__prefix_transitions,
    ``LexLt_cons_iff__prefix_transitions,
    ``LexLt_iff_list_compare__prefix_transitions,
    ``move_from_singleton_iff_earlier_smaller__prefix_transitions,
    ``Z_compare_same_trans__prefix_transitions,
    ``LexLt_trans__prefix_transitions,
    ``LexLt_irrefl__prefix_transitions,
    ``IntervalMove_trans__prefix_transitions,
    ``IntervalMove_capacity_lt__prefix_transitions,
    ``interval_valid_capacity_nonneg__prefix_transitions,
    ``terminal_move_from_valid__prefix_transitions,
    ``terminal_move__prefix_transitions,
    ``AnnWins_iff_move_from_singleton__prefix_transitions,
    ``ann_wins_iff_prefix_min_lt__prefix_transitions,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1_split_goal_3,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_2_1_split_goal_1,
    ``proof_of_solver_entail_wit_2_1_split_goal_2,
    ``proof_of_solver_entail_wit_2_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_1,
    ``proof_of_solver_entail_wit_2_2_split_goal_2,
    ``proof_of_solver_entail_wit_2_2,
    ``proof_of_solver_entail_wit_2_3_split_goal_1,
    ``proof_of_solver_entail_wit_2_3_split_goal_2,
    ``proof_of_solver_entail_wit_2_3,
    ``proof_of_solver_return_wit_1
  ]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
  Lean.logInfo "P030 substring: all 31 source Qed recursively audited without sorryAx"
