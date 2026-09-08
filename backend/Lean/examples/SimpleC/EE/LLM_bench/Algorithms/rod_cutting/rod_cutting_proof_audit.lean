import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal_check

open SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib
open SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_manual

-- All 7 library Qed and 15 manual Qed retain their Coq public names.
-- The 16 source auto Admitted are inherited separately; none may enter these proofs.
run_cmd do
  let proved := #[
    ``rod_cut_scan_best_step__scan_transitions,
    ``rod_cut_positive_sum_nonnegative__table_extension,
    ``rod_cut_positive_sum_member_bound__table_extension,
    ``rod_cut_plan_tail__table_extension,
    ``rod_cut_optimal_revenue_step__table_extension,
    ``rod_cut_revenue_table_snoc__table_extension,
    ``rod_cut_optimal_revenue_zero__boundary_states,
    ``proof_of_rod_cutting_entail_wit_1,
    ``proof_of_rod_cutting_entail_wit_2_split_goal_1,
    ``proof_of_rod_cutting_entail_wit_2_split_goal_2,
    ``proof_of_rod_cutting_entail_wit_2_split_goal_3,
    ``proof_of_rod_cutting_entail_wit_2,
    ``proof_of_rod_cutting_entail_wit_4_1_split_goal_1,
    ``proof_of_rod_cutting_entail_wit_4_1,
    ``proof_of_rod_cutting_entail_wit_4_2_split_goal_1,
    ``proof_of_rod_cutting_entail_wit_4_2,
    ``proof_of_rod_cutting_entail_wit_5_split_goal_1,
    ``proof_of_rod_cutting_entail_wit_5_split_goal_2,
    ``proof_of_rod_cutting_entail_wit_5_split_goal_3,
    ``proof_of_rod_cutting_entail_wit_5_split_goal_4,
    ``proof_of_rod_cutting_entail_wit_5,
    ``proof_of_rod_cutting_return_wit_1]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed rod_cutting proof {decl} depends on sorryAx"
