import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_goal_check

run_cmd do
  let proved := #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.BoundedItem_nil,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.BoundedItem_Znth,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.BoundedItem_append_one,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.BoundedItem_prefix,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.PopTarget_preserves_bounds,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Forall_Znth__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Forall2_Znth__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Forall_removelast__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Zlength_removelast_nonempty__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Spec_step_and_last__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.PopTarget_remove_last__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.PopTarget_last_match__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Znth_last_snoc__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Spec_nonone_pop__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.Spec_one_append__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.stack_append_one_invariant__semantic_transitions,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.sublist_snoc_Znth__flattening_and_completion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.FlatPrefix_snoc__flattening_and_completion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.FlatPrefix_full__flattening_and_completion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.LengthsPrefix_snoc__flattening_and_completion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.LengthsPrefix_full__flattening_and_completion,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_safety_wit_7_split_goal_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_safety_wit_7_split_goal_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_safety_wit_7,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_5_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_5_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_6,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_7,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_8,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_9,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_entail_wit_10,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual.proof_of_solver_return_wit_1
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
  Lean.logInfo "Audited 35 source Qed/Defined declarations; no sorryAx or additional mathematical axioms."
