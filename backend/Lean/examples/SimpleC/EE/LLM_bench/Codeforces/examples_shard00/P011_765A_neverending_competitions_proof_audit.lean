import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_proof_manual

run_cmd do
  let proved := #[
    ``itinerary_endpoint_parity__return_parity,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2_split_goal_1,
    ``proof_of_solver_return_wit_2]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
