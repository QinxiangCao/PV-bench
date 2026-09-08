import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_goal_check

run_cmd do
  let proved := #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.terminal_frequency_summary_implies_Spec,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.length_replace_nth__counting_invariant,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.Zlength_replace_Znth__counting_invariant,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.count_prefix_step__counting_invariant,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.maximum_frequency_prefix_zero__counting_invariant,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.sublist_snoc_at__frequency_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.count_occ_sublist_zero_above__frequency_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.maximum_frequency_prefix_raise__frequency_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.maximum_frequency_prefix_tie__frequency_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.maximum_frequency_prefix_below__frequency_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.two_occurrences_nat_count_occ__terminal_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.two_distinct_Znth_count_occ__terminal_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.Znth_in_range_In__terminal_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.terminal_frequency_bounds__terminal_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_safety_wit_13_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_safety_wit_13_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_safety_wit_13,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_safety_wit_14_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_safety_wit_14_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_safety_wit_14,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_1_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_1_split_goal_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_3_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_3_split_goal_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_3_split_goal_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_4_1_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_4_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_4_2_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_4_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_4_3_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_4_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_5_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_5_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_5_split_goal_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_5_split_goal_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_5_split_goal_5,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_proof_manual.proof_of_solver_entail_wit_5
  ]
  -- Shared C memory-model parameters appear in the types of spatial verification conditions.
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``SimpleC.SL.CNotation.eval_addr_expr, ``SimpleC.SL.CNotation.sizeof_alias_type,
    ``SimpleC.SL.CNotation.sizeof_enum_type, ``SimpleC.SL.CNotation.sizeof_struct_type,
    ``SimpleC.SL.CNotation.sizeof_union_type]
  for decl in proved do
    for ax in (← Lean.collectAxioms decl) do
      unless allowed.contains ax do
        throwError "Source proof {decl} depends on unexpected axiom {ax}"
  Lean.logInfo "Audited 43 source Qed/Defined declarations; no sorryAx or additional mathematical axioms."
