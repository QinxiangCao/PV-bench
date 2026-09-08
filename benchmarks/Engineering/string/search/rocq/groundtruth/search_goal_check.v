From PVbench.Engineering.string.search.rocq.groundtruth Require Import search_goal search_proof_auto search_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include search_proof_auto.
  Include search_proof_manual.
End VC_Correctness.
