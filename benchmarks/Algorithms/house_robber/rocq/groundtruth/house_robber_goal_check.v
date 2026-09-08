From PVbench.Algorithms.house_robber.rocq.groundtruth Require Import house_robber_goal house_robber_proof_auto house_robber_proof_manual.

Module VC_Correctness : VC_Correct.
  Include house_robber_proof_auto.
  Include house_robber_proof_manual.
End VC_Correctness.
