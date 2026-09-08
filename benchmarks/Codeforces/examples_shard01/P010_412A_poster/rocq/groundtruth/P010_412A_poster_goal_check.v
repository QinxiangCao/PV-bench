From PVbench.Codeforces.examples_shard01.P010_412A_poster.rocq.groundtruth Require Import P010_412A_poster_goal P010_412A_poster_proof_auto P010_412A_poster_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include char_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P010_412A_poster_proof_auto.
  Include P010_412A_poster_proof_manual.
End VC_Correctness.
