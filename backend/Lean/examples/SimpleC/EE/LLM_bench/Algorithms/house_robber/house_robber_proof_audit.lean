import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal_check

-- All 33 source Qed declarations: 27 library lemmas and six manual proofs.
run_cmd do
  let completed : List Lean.Name := [
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.RobPrefixOpt_zero,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_prefix_opt_elim,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_prefix_opt_intro,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_plan_value_nonneg_bound,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.NoDup_remove_Z,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.NoDup_map_Z_to_nat,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.NoDup_range_length,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_prefix_value_bound_by_len,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_prefix_opt_bound_by_len,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.nonadj_drop_last_notin,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.nonadj_single_zero,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.nonadj_cons_current,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.nonadj_remove_current,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.remove_zero_range_one_nil,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_plan_value_remove,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.rob_prefix_step_take,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.house_robber_dp_step_take,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.house_robber_take_value_bound,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.NonAdjacentIndexList_extend,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.RobPrefixValue_extend,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.NonAdjacentIndexList_drop_last_notin,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.NonAdjacentIndexList_remove_current,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.RobPlanValue_remove_in,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.RobPlanValue_limit_one_in,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.RobPrefixValue_remove_current,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.RobPrefixOpt_step_skip,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.HouseRobberDPState_skip_step,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual.proof_of_rob_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual.proof_of_rob_entail_wit_2_2,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual.proof_of_rob_entail_wit_2_1,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual.proof_of_rob_entail_wit_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual.proof_of_rob_entail_wit_3,
    ``SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual.proof_of_rob_return_wit_1
  ]
  for decl in completed do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed proof {decl} depends on sorryAx"
  Lean.logInfo "Checked all 33 source Qed declarations: no recursive sorryAx dependencies."
