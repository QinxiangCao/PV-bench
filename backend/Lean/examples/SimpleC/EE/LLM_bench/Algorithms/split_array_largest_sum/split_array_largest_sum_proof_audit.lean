import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_goal_check

open SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib
open SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_manual

-- All 35 lib and 13 manual source Qed declarations; 20 auto Admitted inherited separately.
run_cmd do
  let proved := #[
    ``minimized_partition_witness,
    ``minimized_lower_bound,
    ``minmax_not_partition_below,
    ``can_split_cannot_contradiction,
    ``mid_quot_bounds,
    ``prefix_split_state_zero,
    ``prefix_split_state_step_over_cap,
    ``prefix_split_state_extend_no_split,
    ``PrefixSplitState_items_bound,
    ``PrefixSplitState_unique,
    ``sum_snoc,
    ``sublist_snoc_Znth,
    ``prefix_state_partition,
    ``can_split_bounded_partition_at_most,
    ``max_segment_sum_exists,
    ``sum_nonnegative,
    ``sublist_cons_tail,
    ``prefix_state_cur_bounds,
    ``process_segment_no_new,
    ``process_segment_one_new,
    ``app_eq_same_zlength,
    ``split_sublist_at_prefix,
    ``process_parts_one_new_each,
    ``bounded_partition_to_can_split,
    ``in_list_nonnegative,
    ``partition_max_segments_good,
    ``partition_max_to_can_split,
    ``refine_partition_once,
    ``refine_partition_to_target_fuel,
    ``refine_partition_to_target,
    ``max_segment_sum_bound,
    ``good_segments_nonnil,
    ``can_split_to_partition_max,
    ``minmax_can_lower_bound,
    ``minmax_cannot_upper_bound,
    ``proof_of_check_entail_wit_1,
    ``proof_of_check_entail_wit_2_1,
    ``proof_of_check_entail_wit_2_2,
    ``proof_of_check_return_wit_1,
    ``proof_of_check_return_wit_2,
    ``proof_of_check_return_wit_3,
    ``proof_of_splitArrayLargestSum_safety_wit_3,
    ``proof_of_splitArrayLargestSum_safety_wit_7,
    ``proof_of_splitArrayLargestSum_entail_wit_1,
    ``proof_of_splitArrayLargestSum_entail_wit_2_1,
    ``proof_of_splitArrayLargestSum_entail_wit_2_2,
    ``proof_of_splitArrayLargestSum_partial_solve_wit_1_pure,
    ``proof_of_splitArrayLargestSum_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed split_array_largest_sum proof {decl} depends on sorryAx"
