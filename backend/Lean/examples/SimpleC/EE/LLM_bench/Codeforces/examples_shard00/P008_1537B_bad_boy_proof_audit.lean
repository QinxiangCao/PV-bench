import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_goal_check

-- The two source library lemmas and the manual return proof were closed by Qed.
-- The ten source auto Admitted declarations remain the only inherited holes.
run_cmd do
  let completed : List Lean.Name := [
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib.cycle_span_bound__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib.opposite_corners_spec__final_result,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_proof_manual.proof_of_solver_return_wit_1
  ]
  for decl in completed do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Completed proof {decl} depends on sorryAx"
  Lean.logInfo "Checked all 3 source Qed declarations: no recursive sorryAx dependencies."
