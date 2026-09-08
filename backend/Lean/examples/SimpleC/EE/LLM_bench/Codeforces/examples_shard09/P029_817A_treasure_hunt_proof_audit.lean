import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_goal_check
import Lean.Util.CollectAxioms
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_proof_manual

-- Each source Qed, including split helpers, must remain independent of inherited holes.
run_cmd do
  for decl in #[
    ``proof_of_solver_entail_wit_1_1_split_goal_1 ,
    ``proof_of_solver_entail_wit_1_1 ,
    ``proof_of_solver_entail_wit_1_2_split_goal_1 ,
    ``proof_of_solver_entail_wit_1_2 ,
    ``proof_of_solver_entail_wit_2_1_split_goal_1 ,
    ``proof_of_solver_entail_wit_2_1 ,
    ``proof_of_solver_entail_wit_2_2_split_goal_1 ,
    ``proof_of_solver_entail_wit_2_2 ,
    ``proof_of_solver_return_wit_1_split_goal_1 ,
    ``proof_of_solver_return_wit_1 ,
    ``proof_of_solver_return_wit_2_split_goal_1 ,
    ``proof_of_solver_return_wit_2 ,
    ``proof_of_solver_return_wit_3_split_goal_1 ,
    ``proof_of_solver_return_wit_3 ,
    ``proof_of_solver_return_wit_4_split_goal_1 ,
    ``proof_of_solver_return_wit_4] do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Source Qed {decl} depends on sorryAx"

