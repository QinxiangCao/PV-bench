Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition SegmentPartition (l : list Z) (parts : list (list Z)) : Prop :=
  parts <> [] /\
  concat parts = l /\
  Forall (fun seg => seg <> []) parts.
Definition MaxSegmentSum (parts : list (list Z)) (max_sum : Z) : Prop :=
  max_value_of_subset Z.le
    (fun seg => In seg parts)
    (fun seg => sum seg)
    max_sum.
Definition PartitionMaxSegmentSum (l : list Z) (m max_sum : Z) : Prop :=
  exists parts,
    SegmentPartition l parts /\
    Zlength parts = m /\
    MaxSegmentSum parts max_sum.
Definition MinimizedMaxSegmentSum (l : list Z) (m answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun max_sum => PartitionMaxSegmentSum l m max_sum)
    (fun max_sum => max_sum)
    answer.
