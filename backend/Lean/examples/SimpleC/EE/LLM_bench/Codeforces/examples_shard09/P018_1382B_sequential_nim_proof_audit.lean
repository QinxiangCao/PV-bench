import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_proof_manual

-- The 4 source library Qed and 11 source manual Qed must not depend on
-- the 11 inherited auto Admitted declarations.
run_cmd do
  let proved := #[
    ``leading_ones_unique__return_semantics,
    ``even_of_nonnegative_rem_zero__return_semantics,
    ``odd_of_nonnegative_rem_nonzero__return_semantics,
    ``even_of_nonnegative_rem_not_one__return_semantics,
    ``proof_of_solver_entail_wit_1_split_goal_1,
    ``proof_of_solver_entail_wit_1_split_goal_2,
    ``proof_of_solver_entail_wit_1,
    ``proof_of_solver_entail_wit_3_1_split_goal_1,
    ``proof_of_solver_entail_wit_3_1,
    ``proof_of_solver_entail_wit_3_2_split_goal_1,
    ``proof_of_solver_entail_wit_3_2,
    ``proof_of_solver_return_wit_1,
    ``proof_of_solver_return_wit_2,
    ``proof_of_solver_return_wit_3,
    ``proof_of_solver_return_wit_4]
  for decl in proved do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"
