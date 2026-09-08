From PVbench.Codeforces.examples_shard01.P082_623B_array_gcd.rocq.groundtruth Require Import P082_623B_array_gcd_goal P082_623B_array_gcd_proof_auto P082_623B_array_gcd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P082_623B_array_gcd_proof_auto.
  Include P082_623B_array_gcd_proof_manual.
End VC_Correctness.
