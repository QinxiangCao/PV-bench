Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Unlimited reuse is the library reflexive-transitive closure of adding a coin. *)
Definition ReachableAmount (coins : list Z) (v : Z) : Prop :=
  Relation_Operators.clos_refl_trans Z
    (fun u w => exists c, In c coins /\ 0 < c /\ w = u + c) 0 v.

Definition MaxReachableAmount (coins : list Z) (amount ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => ReachableAmount coins v /\ 0 <= v /\ v <= amount)
    (fun v => v) ans.
