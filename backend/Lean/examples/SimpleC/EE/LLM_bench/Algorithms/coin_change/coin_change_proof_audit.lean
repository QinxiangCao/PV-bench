import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal_check

-- The 12 library and 17 manual lemmas completed by Qed in the Coq source.
run_cmd do
  let completed : List Lean.Name := [
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.MaxReachableAmount_intro_no_above,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_nil_inv,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.DpPrefixZeroed_snoc_zero,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.DpPrefixZeroed_to_DpReachableTable_nil,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_nonneg,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_mono_incl,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_app_single_below,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.DpCoinInnerProgress_replace_current,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_app_l,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_app_single_inv,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.ReachableAmount_app_single_lt,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.sublist_0_succ_app,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_3,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_4,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_5,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_6,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_7,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_8_1,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_8_2,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_9_2,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_9_1,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_10_split_goal_1,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_10,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_11,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_12,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_13_1,
    ``SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual.proof_of_coinChange_entail_wit_13_2
  ]
  for decl in completed do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed proof {decl} depends on sorryAx"
  Lean.logInfo "Checked all 29 source Qed declarations: no recursive sorryAx dependencies."
