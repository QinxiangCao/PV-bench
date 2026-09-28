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
From PVbench.Algorithms.climbing_stairs.rocq.groundtruth Require Import climbing_stairs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import PVbench.Algorithms.climbing_stairs.rocq.spec_lib.
Require Import PVbench.Algorithms.climbing_stairs.rocq.helper_lib.
Local Open Scope sac.

Lemma proof_of_climbStairs_safety_wit_1 : climbStairs_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_climbStairs_safety_wit_2 : climbStairs_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_climbStairs_safety_wit_3 : climbStairs_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_climbStairs_safety_wit_5 : climbStairs_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_climbStairs_safety_wit_6 : climbStairs_safety_wit_6.
Proof. Admitted. 

