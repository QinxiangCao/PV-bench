import Algorithms.house_robber.lean.groundtruth.house_robber_proof_auto
import Algorithms.house_robber.lean.groundtruth.house_robber_proof_manual

namespace Algorithms.house_robber.lean.groundtruth.house_robber_goal_check

open Algorithms.house_robber.lean.groundtruth.house_robber_proof_auto
open Algorithms.house_robber.lean.groundtruth.house_robber_proof_manual

def VC_Correctness : Algorithms.house_robber.lean.groundtruth.house_robber_goal.VC_Correct where
  proof_of_rob_safety_wit_1 := proof_of_rob_safety_wit_1
  proof_of_rob_safety_wit_2 := proof_of_rob_safety_wit_2
  proof_of_rob_safety_wit_3 := proof_of_rob_safety_wit_3
  proof_of_rob_safety_wit_4 := proof_of_rob_safety_wit_4
  proof_of_rob_safety_wit_5 := proof_of_rob_safety_wit_5
  proof_of_rob_partial_solve_wit_1 := proof_of_rob_partial_solve_wit_1
  proof_of_rob_entail_wit_1 := proof_of_rob_entail_wit_1
  proof_of_rob_entail_wit_2_1 := proof_of_rob_entail_wit_2_1
  proof_of_rob_entail_wit_2_2 := proof_of_rob_entail_wit_2_2
  proof_of_rob_entail_wit_3 := proof_of_rob_entail_wit_3
  proof_of_rob_return_wit_1 := proof_of_rob_return_wit_1

end Algorithms.house_robber.lean.groundtruth.house_robber_goal_check
