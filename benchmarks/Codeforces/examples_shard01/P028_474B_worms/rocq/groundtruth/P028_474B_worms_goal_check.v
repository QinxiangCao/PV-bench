From PVbench.Codeforces.examples_shard01.P028_474B_worms.rocq.groundtruth Require Import P028_474B_worms_goal P028_474B_worms_proof_auto P028_474B_worms_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P028_474B_worms_proof_auto.
  Include P028_474B_worms_proof_manual.
End VC_Correctness.
