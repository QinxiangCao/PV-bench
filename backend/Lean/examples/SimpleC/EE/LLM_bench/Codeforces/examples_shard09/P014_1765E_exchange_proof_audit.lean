import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_proof_manual

run_cmd do
  let proved := #[
    ``exchange_prepend_steps__exchange_minimum,
    ``exchange_prepend_last__exchange_minimum,
    ``exchange_sell_path__exchange_minimum,
    ``exchange_sell_trace__exchange_minimum,
    ``exchange_path_potential__exchange_minimum,
    ``exchange_nonprofitable_lower_bound__exchange_minimum,
    ``exchange_cycle_path__exchange_minimum,
    ``exchange_profitable_one_reachable__exchange_minimum,
    ``exchange_zero_unreachable__exchange_minimum,
    ``exchange_nonprofitable_spec__exchange_minimum,
    ``exchange_profitable_spec__exchange_minimum,
    ``proof_of_solver_return_wit_1_split_goal_1,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2_split_goal_1,
    ``proof_of_solver_return_wit_2]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
