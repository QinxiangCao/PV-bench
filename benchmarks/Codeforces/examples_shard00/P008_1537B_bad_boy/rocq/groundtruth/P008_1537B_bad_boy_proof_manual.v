Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import PVbench.Codeforces.examples_shard00.P008_1537B_bad_boy.rocq.groundtruth.P008_1537B_bad_boy_goal.
Require Import PVbench.Codeforces.examples_shard00.P008_1537B_bad_boy.rocq.groundtruth.P008_1537B_bad_boy_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import PVbench.Codeforces.examples_shard00.P008_1537B_bad_boy.rocq.groundtruth.proof_lib.
Local Open Scope sac.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (1, 1) (n_pre, m_pre).
  split_pure_spatial.
  - simpl.
    rewrite Int64Array.undef_seg_empty.
    Int64Array.ArraySimplify.
    simpl.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      lia.
  - dump_pre_spatial.
    apply opposite_corners_spec__final_result.
    + lia.
    + lia.
    + unfold InRoom.
      simpl in *.
      lia.
Qed.
