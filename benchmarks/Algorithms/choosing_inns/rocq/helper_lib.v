Require Import PVbench.Algorithms.choosing_inns.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition color_count (colors : list Z) (limit color : Z) : Z :=
  Z.of_nat
    (length
       (filter (fun idx => Z.eqb (Znth idx colors 0) color)
               (zrange limit))).
Definition good_color_count
    (colors costs : list Z) (limit p color : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun idx =>
             Z.eqb (Znth idx colors 0) color &&
             affordable_betweenb costs p idx (limit - 1))
          (zrange limit))).

(** Safety and representation facts for the immutable problem input.  This
    predicate deliberately contains no statement about the required answer. *)
Definition CountArraySafe (xs : list Z) (k limit : Z) : Prop :=
  Zlength xs = k /\
  forall idx, 0 <= idx < k -> 0 <= Znth idx xs 0 <= limit.
Definition CountsZeroPrefix (xs : list Z) (written : Z) : Prop :=
  Zlength xs = written /\
  forall idx, 0 <= idx < written -> Znth idx xs 0 = 0.
Definition CountsZeroFull (k : Z) (xs : list Z) : Prop :=
  Zlength xs = k /\
  forall idx, 0 <= idx < k -> Znth idx xs 0 = 0.
Definition CopyCountsPrefix
    (src old dst : list Z) (written k : Z) : Prop :=
  (forall idx, 0 <= idx < written -> Znth idx dst 0 = Znth idx src 0) /\
  (forall idx, written <= idx < k -> Znth idx dst 0 = Znth idx old 0).

(** Safety facts for the mutable prefix state.  The mathematical meanings of
    [answer], [seen], and [good] are intentionally absent. *)
Definition ChoosingPrefixDataSafe
    (colors costs : list Z) (limit k : Z) (seen good : list Z) : Prop :=
  0 <= limit <= Zlength colors /\
  Zlength costs = Zlength colors /\
  CountArraySafe seen k limit /\
  CountArraySafe good k limit.

(** Functional meaning of a processed prefix, independent of C array shape
    and machine-integer bounds. *)
Definition ChoosingPrefixState
    (colors costs : list Z) (limit k p answer : Z)
    (seen good : list Z) : Prop :=
  answer = choosing_pair_count colors costs p limit /\
  (forall color,
      0 <= color < k ->
      Znth color seen 0 = color_count colors limit color) /\
  (forall color,
      0 <= color < k ->
      Znth color good 0 = good_color_count colors costs limit p color).
