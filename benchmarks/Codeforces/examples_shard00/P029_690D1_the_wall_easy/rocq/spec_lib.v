Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition NonemptyWallColumn (grid : list (list Z)) (col : Z) : Prop :=
  exists row, 0 <= row < Zlength grid /\ Znth col (Znth row grid nil) 0 = 66.

Definition StartsWallSegment (grid : list (list Z)) (col : Z) : Prop :=
  0 <= col < Zlength (Znth 0 grid nil) /\
  NonemptyWallColumn grid col /\
  (col = 0 \/ ~ NonemptyWallColumn grid (col - 1)).

Definition Pre (r c : Z) (grid : list (list Z)) : Prop :=
  1 <= r <= 100 /\ 1 <= c <= 100 /\ Zlength grid = r /\
  Forall (fun row => Zlength row = c /\
    Forall (fun cell => cell = 66 \/ cell = 46) row) grid.

Definition Spec (r c : Z) (grid : list (list Z)) (out : Z) : Prop :=
  out = #(fun col : Z =>
    0 <= col < Zlength (Znth 0 grid nil) /\ StartsWallSegment grid col).
