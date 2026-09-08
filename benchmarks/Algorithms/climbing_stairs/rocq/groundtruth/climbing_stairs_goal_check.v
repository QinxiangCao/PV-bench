From PVbench.Algorithms.climbing_stairs.rocq.groundtruth Require Import climbing_stairs_goal climbing_stairs_proof_auto climbing_stairs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include climbing_stairs_proof_auto.
  Include climbing_stairs_proof_manual.
End VC_Correctness.
