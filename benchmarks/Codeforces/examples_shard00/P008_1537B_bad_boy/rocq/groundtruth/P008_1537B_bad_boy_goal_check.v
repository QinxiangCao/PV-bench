From PVbench.Codeforces.examples_shard00.P008_1537B_bad_boy.rocq.groundtruth Require Import P008_1537B_bad_boy_goal P008_1537B_bad_boy_proof_auto P008_1537B_bad_boy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P008_1537B_bad_boy_proof_auto.
  Include P008_1537B_bad_boy_proof_manual.
End VC_Correctness.
