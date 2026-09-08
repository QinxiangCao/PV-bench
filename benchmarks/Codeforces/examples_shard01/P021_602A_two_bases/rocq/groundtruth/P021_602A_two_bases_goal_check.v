From PVbench.Codeforces.examples_shard01.P021_602A_two_bases.rocq.groundtruth Require Import P021_602A_two_bases_goal P021_602A_two_bases_proof_auto P021_602A_two_bases_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P021_602A_two_bases_proof_auto.
  Include P021_602A_two_bases_proof_manual.
End VC_Correctness.
