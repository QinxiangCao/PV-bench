From PVbench.Codeforces.examples_shard00.P050_440B_balancer.rocq.groundtruth Require Import P050_440B_balancer_goal P050_440B_balancer_proof_auto P050_440B_balancer_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P050_440B_balancer_proof_auto.
  Include P050_440B_balancer_proof_manual.
End VC_Correctness.
