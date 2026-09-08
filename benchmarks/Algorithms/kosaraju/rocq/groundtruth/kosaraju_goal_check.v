From PVbench.Algorithms.kosaraju.rocq.groundtruth Require Import kosaraju_goal kosaraju_proof_auto kosaraju_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include kosaraju_proof_auto.
  Include kosaraju_proof_manual.
End VC_Correctness.
