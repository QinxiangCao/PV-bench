import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal_check

open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_proof_manual

-- Check all 9 source library Qed, all 11 source manual Qed, and all 16
-- additional named split-goal proofs. The 14 Coq auto Admitted are inherited
-- separately and must not enter any of these completed proofs.
run_cmd do
  let proved := #[
    ``sum_sublist_single,
    ``sum_sublist_snoc,
    ``MaxSuffixSumPrefix_single,
    ``MaxSubarraySumPrefix_single,
    ``MaxSuffixSumPrefix_step,
    ``MaxSubarraySumPrefix_step,
    ``sum_upper_bound,
    ``sum_sublist_upper_bound,
    ``MaxSuffixSumPrefix_upper_bound,
    ``proof_of_max_return_wit_1_split_goal_1,
    ``proof_of_max_return_wit_2_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_1_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_1_split_goal_2,
    ``proof_of_max_sub_array_entail_wit_1_split_goal_3,
    ``proof_of_max_sub_array_entail_wit_2_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_3_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_4_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_4_split_goal_2,
    ``proof_of_max_sub_array_entail_wit_4_split_goal_3,
    ``proof_of_max_sub_array_entail_wit_4_split_goal_4,
    ``proof_of_max_sub_array_entail_wit_5_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_5_split_goal_2,
    ``proof_of_max_sub_array_entail_wit_5_split_goal_3,
    ``proof_of_max_sub_array_entail_wit_5_split_goal_4,
    ``proof_of_max_sub_array_entail_wit_6_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_7_split_goal_1,
    ``proof_of_max_sub_array_entail_wit_7_split_goal_2,
    ``proof_of_max_return_wit_1,
    ``proof_of_max_return_wit_2,
    ``proof_of_max_sub_array_entail_wit_1,
    ``proof_of_max_sub_array_entail_wit_2,
    ``proof_of_max_sub_array_entail_wit_3,
    ``proof_of_max_sub_array_entail_wit_4,
    ``proof_of_max_sub_array_entail_wit_5,
    ``proof_of_max_sub_array_entail_wit_6,
    ``proof_of_max_sub_array_entail_wit_7]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed maximum_subarray proof {decl} depends on sorryAx"
