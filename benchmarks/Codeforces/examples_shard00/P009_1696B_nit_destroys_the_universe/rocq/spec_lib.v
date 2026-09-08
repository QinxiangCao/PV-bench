Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition SegmentMex (a : list Z) (l r w : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z =>
      0 <= candidate /\
      forall i, l <= i <= r -> Znth i a 0 <> candidate)
    (fun candidate => candidate) w.

Definition OneSnap (before after : list Z) : Prop :=
  exists l r w,
    0 <= l <= r /\ r < Zlength before /\
    SegmentMex before l r w /\
    Zlength after = Zlength before /\
    forall i, 0 <= i < Zlength before ->
      Znth i after 0 =
        if andb (l <=? i) (i <=? r) then w else Znth i before 0.

Definition SnapTrace (initial : list Z) (states : list (list Z)) : Prop :=
  0 < Zlength states /\
  Znth 0 states [] = initial /\
  (forall k, 0 <= k < Zlength states - 1 ->
     OneSnap (Znth k states []) (Znth (k + 1) states [])) /\
  Forall (fun x => x = 0) (Znth (Zlength states - 1) states []).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 100000 /\
  Forall (fun x => 0 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (SnapTrace a)
    (fun states => Zlength states - 1) out.
