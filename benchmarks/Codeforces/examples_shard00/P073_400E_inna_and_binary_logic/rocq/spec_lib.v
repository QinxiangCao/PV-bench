Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition AndExerciseSum (a : list Z) : Z :=
  fold_right Z.add 0
    (map (fun p => let '(l,r) := p in
      fold_left Z.land (sublist l (r+1) a) (-1))
      (concat (Zmap_range
        (fun l => map (fun r => (l,r)) (Zrange l (Zlength a)))
        (Zlength a)))).

Definition ApplyPointUpdate (a : list Z) (u : Z * Z) : list Z :=
  replace_Znth (fst u) (snd u) a.

Definition Pre (a : list Z) (updates : list (Z * Z)) : Prop :=
  1 <= Zlength a <= 100000 /\ 1 <= Zlength updates <= 100000 /\
  Forall (fun x => 0 <= x <= 100000) a /\
  Forall (fun u => 0 <= fst u < Zlength a /\ 0 <= snd u <= 100000) updates.

Definition Spec (a : list Z) (updates : list (Z * Z)) (out : list Z) : Prop :=
  exists states,
    Zlength states = Zlength updates + 1 /\ Znth 0 states nil = a /\
    (forall i, 0 <= i < Zlength updates ->
      Znth (i+1) states nil = ApplyPointUpdate (Znth i states nil) (Znth i updates (0,0))) /\
    Zlength out = Zlength updates /\
    forall i, 0 <= i < Zlength out ->
      Znth i out 0 = AndExerciseSum (Znth (i+1) states nil).

Require Import Coq.micromega.Psatz.

Require Import Coq.micromega.Lia.
