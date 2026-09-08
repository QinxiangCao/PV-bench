From PVbench.Algorithms.majority_element.rocq.groundtruth Require Import majority_element_goal majority_element_proof_auto majority_element_proof_manual.

Module VC_Correctness : VC_Correct.
  Include majority_element_proof_auto.
  Include majority_element_proof_manual.
End VC_Correctness.
