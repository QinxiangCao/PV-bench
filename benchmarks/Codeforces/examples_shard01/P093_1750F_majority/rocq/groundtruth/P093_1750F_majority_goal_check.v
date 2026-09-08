From PVbench.Codeforces.examples_shard01.P093_1750F_majority.rocq.groundtruth Require Import P093_1750F_majority_goal P093_1750F_majority_proof_auto P093_1750F_majority_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P093_1750F_majority_proof_auto.
  Include P093_1750F_majority_proof_manual.
End VC_Correctness.
