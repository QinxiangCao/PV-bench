From PVbench.Codeforces.examples_shard00.P045_569A_music.rocq.groundtruth Require Import P045_569A_music_goal P045_569A_music_proof_auto P045_569A_music_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P045_569A_music_proof_auto.
  Include P045_569A_music_proof_manual.
End VC_Correctness.
