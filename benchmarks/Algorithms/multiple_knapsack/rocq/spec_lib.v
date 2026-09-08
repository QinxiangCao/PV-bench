Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition PairwiseWeightValue (xs : list (Z * Z)) : Z :=
  sum (map (fun wp => fst wp * snd wp) xs).
Definition PickWeight (weights picks : list Z) : Z :=
  PairwiseWeightValue (combine weights picks).
Definition PickValue (values picks : list Z) : Z :=
  PairwiseWeightValue (combine values picks).
Definition BoundedPickList
    (weights values counts : list Z) (capacity : Z) (picks : list Z) : Prop :=
  Zlength weights = Zlength values /\
  Zlength weights = Zlength counts /\
  Zlength picks = Zlength weights /\
  0 <= capacity /\
  Forall2 (fun pick cnt => 0 <= pick <= cnt) picks counts /\
  0 <= PickWeight weights picks /\
  PickWeight weights picks <= capacity.
Definition MultipleKnapsackAnswer
    (weights values counts : list Z) (capacity answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun picks => BoundedPickList weights values counts capacity picks)
    (fun picks => PickValue values picks)
    answer.
Definition MultipleKnapsackPrefixAnswer
    (weights values counts : list Z) (i capacity answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun picks =>
       BoundedPickList
         (sublist 0 i weights)
         (sublist 0 i values)
         (sublist 0 i counts)
         capacity
         picks)
    (fun picks => PickValue (sublist 0 i values) picks)
    answer.
Definition MKScratchArraysSafety
    (old q_idx q_val : list Z) (capacity : Z) : Prop :=
  Zlength old = capacity + 1 /\
  Zlength q_idx = capacity + 1 /\
  Zlength q_val = capacity + 1.
Definition MKDPTableSafety
    (weights : list Z) (i capacity : Z) (dp : list Z) : Prop :=
  0 <= i <= Zlength weights /\
  0 <= capacity /\
  Zlength dp = capacity + 1.
Definition MKDPTableSemantics
    (weights values counts : list Z) (i capacity : Z) (dp : list Z) : Prop :=
  forall cap,
    0 <= cap <= capacity ->
    MultipleKnapsackPrefixAnswer weights values counts i cap (Znth cap dp 0).
