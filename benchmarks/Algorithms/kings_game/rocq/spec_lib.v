Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition minister : Type := (Z * Z)%type.
Definition mk_minister (left right : Z) : minister := (left, right).
Definition minister_left (p : minister) : Z := fst p.
Definition minister_right (p : minister) : Z := snd p.
Definition minister_product (p : minister) : Z :=
  minister_left p * minister_right p.
Definition default_minister : minister := mk_minister 1 1.

(** The memory relation deliberately says only how a mathematical sequence
    of ministers is flattened into the C int array. *)
Definition minister_flatten (ps : list minister) : list Z :=
  flat_map (fun p => [minister_left p; minister_right p]) ps.
Definition FlatMinisters (flat : list Z) (ps : list minister) : Prop :=
  flat = minister_flatten ps.
Definition MinisterHandsBound (ps : list minister) : Prop :=
  Forall
    (fun p =>
       1 <= minister_left p <= 10 /\
       1 <= minister_right p <= 10)
    ps.
Definition MinisterPermutation : list minister -> list minister -> Prop :=
  @Permutation minister.

(** The greedy key and its mathematical sortedness property. *)
Definition MinisterProductLe (p q : minister) : Prop :=
  minister_product p <= minister_product q.
Definition MinisterSorted (ps : list minister) : Prop :=
  forall i j,
    0 <= i -> i <= j -> j < Zlength ps ->
    MinisterProductLe
      (Znth i ps default_minister)
      (Znth j ps default_minister).

(** Product of all left hands strictly before [i].  This is a mathematical
    prefix product, not a mirror of either sorting loop in the C program. *)
Definition PrefixLeftProduct (ps : list minister) (i : Z) : Z :=
  fold_right Z.mul 1
    (map minister_left (sublist 0 i ps)).
Definition MinisterReward
    (king_left : Z) (ps : list minister) (i : Z) : Z :=
  (king_left * PrefixLeftProduct ps i) /
  minister_right (Znth i ps default_minister).

(** The largest reward for one fixed order is defined with MaxMinLib. *)
Definition OrderMaxReward
    (king_left : Z) (ps : list minister) (reward : Z) : Prop :=
  max_value_of_subset Z.le
    (fun i : Z => 0 <= i < Zlength ps)
    (fun i => MinisterReward king_left ps i)
    reward.

(** Candidates for the outer minimization pair an order with the maximum
    reward realised by that order. *)
Definition ValidOrderReward
    (input : list minister) (king_left : Z)
    (candidate : list minister * Z) : Prop :=
  MinisterPermutation input (fst candidate) /\
  OrderMaxReward king_left (fst candidate) (snd candidate).

(** The problem's minimax optimum: minimum, over every permutation of the
    input ministers, of that order's maximum reward. *)
Definition KingsGameOptimum
    (input : list minister) (king_left optimum : Z) : Prop :=
  min_value_of_subset Z.le
    (ValidOrderReward input king_left)
    (@snd (list minister) Z)
    optimum.

(** Final business predicate exposed to the C specification.  In particular,
    the output itself realises the MaxMinLib-defined optimum; sortedness alone
    is not accepted as the result. *)
Definition KingsGameResult
    (input : list minister) (king_left : Z) (output : list minister) : Prop :=
  MinisterPermutation input output /\
  MinisterSorted output /\
  exists reward,
    OrderMaxReward king_left output reward /\
    KingsGameOptimum input king_left reward.

(** Exact mathematical effects of swapping two flat minister records. *)
