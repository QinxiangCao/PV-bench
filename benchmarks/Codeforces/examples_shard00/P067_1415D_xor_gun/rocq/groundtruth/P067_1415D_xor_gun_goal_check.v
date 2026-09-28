From PVbench.Codeforces.examples_shard00.P067_1415D_xor_gun.rocq.groundtruth Require Import P067_1415D_xor_gun_goal P067_1415D_xor_gun_proof_auto P067_1415D_xor_gun_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P067_1415D_xor_gun_proof_auto.
  Include P067_1415D_xor_gun_proof_manual.
End VC_Correctness.
