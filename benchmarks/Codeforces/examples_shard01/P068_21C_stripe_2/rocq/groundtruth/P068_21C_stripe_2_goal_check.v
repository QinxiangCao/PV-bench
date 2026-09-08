From PVbench.Codeforces.examples_shard01.P068_21C_stripe_2.rocq.groundtruth Require Import P068_21C_stripe_2_goal P068_21C_stripe_2_proof_auto P068_21C_stripe_2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P068_21C_stripe_2_proof_auto.
  Include P068_21C_stripe_2_proof_manual.
End VC_Correctness.
