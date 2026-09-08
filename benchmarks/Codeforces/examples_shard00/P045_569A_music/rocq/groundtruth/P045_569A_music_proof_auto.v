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
From PVbench.Codeforces.examples_shard00.P045_569A_music.rocq.groundtruth Require Import P045_569A_music_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import PVbench.Codeforces.examples_shard00.P045_569A_music.rocq.spec_lib.
Require Import PVbench.Codeforces.examples_shard00.P045_569A_music.rocq.helper_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof. Admitted. 

