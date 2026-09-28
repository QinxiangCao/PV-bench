Require Export PVbench.Algorithms.split_array_largest_sum.rocq.spec_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
(* Facts connecting the greedy splitter state with partition semantics. *)
Local Open Scope list_scope.
Require Import Coq.Relations.Relation_Operators.
Require Import AUXLib.MonotonicList.

Definition SplitFeasible (l : list Z) (m cap : Z) : Prop :=
  exists max_sum, PartitionMaxSegmentSum l m max_sum /\ max_sum <= cap.

Definition SplitInfeasible (l : list Z) (m cap : Z) : Prop :=
  ~ SplitFeasible l m cap.

(** Among all legal partitions of the processed prefix, minimize the segment
    count and then the last segment's sum.  The empty prefix has one open,
    empty segment, matching cnt = 1 and cur = 0.  This is a property of
    partitions, independent of a greedy execution history. *)
Definition SplitProgress (prefix : list Z) (cap cnt cur : Z) : Prop :=
  min_value_of_subset
    (fun a b : Z * Z => fst a < fst b \/ (fst a = fst b /\ snd a <= snd b))
    (fun parts : list (list Z) => concat parts = prefix /\
      Forall (fun segment => segment <> [] /\ sum segment <= cap) parts)
    (fun parts => (Z.max 1 (Zlength parts), sum (last parts []))) (cnt, cur).
