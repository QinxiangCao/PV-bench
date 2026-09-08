From PVbench.Codeforces.examples_shard01.P040_81A_plug_in.rocq.groundtruth Require Import P040_81A_plug_in_goal P040_81A_plug_in_proof_auto P040_81A_plug_in_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P040_81A_plug_in_proof_auto.
  Include P040_81A_plug_in_proof_manual.
End VC_Correctness.
