From PVbench.Codeforces.examples_shard01.P075_1474D_cleaning.rocq.groundtruth Require Import P075_1474D_cleaning_goal P075_1474D_cleaning_proof_auto P075_1474D_cleaning_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P075_1474D_cleaning_proof_auto.
  Include P075_1474D_cleaning_proof_manual.
End VC_Correctness.
