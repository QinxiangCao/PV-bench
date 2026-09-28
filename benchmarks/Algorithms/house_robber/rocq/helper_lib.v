Require Export PVbench.Algorithms.house_robber.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition RobPrefixOpt (l : list Z) (len answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value => RobPrefixValue l len value)
    (fun value => value)
    answer.

Definition HouseRobberDPState
    (l : list Z) (i prev2 prev1 : Z) : Prop :=
  RobPrefixOpt l i prev1 /\
  ((i = 0 /\ prev2 = 0) \/
   (0 < i /\ RobPrefixOpt l (i - 1) prev2)).
