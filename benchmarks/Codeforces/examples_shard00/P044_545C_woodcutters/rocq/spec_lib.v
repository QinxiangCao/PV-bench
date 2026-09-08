Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition TreeOccupation (tree : Z*Z) (choice left right : Z) : Prop :=
  (choice = -1 /\ left = fst tree - snd tree /\ right = fst tree) \/
  (choice = 0 /\ left = fst tree /\ right = fst tree) \/
  (choice = 1 /\ left = fst tree /\ right = fst tree + snd tree).

Definition ValidFelling (trees : list (Z*Z)) (choices : list Z) : Prop :=
  Zlength choices = Zlength trees /\ Forall (fun d => d = -1 \/ d = 0 \/ d = 1) choices /\
  forall i, 0 <= i < Zlength trees - 1 -> exists li ri lj rj,
    TreeOccupation (Znth i trees (0,0)) (Znth i choices 0) li ri /\
    TreeOccupation (Znth (i+1) trees (0,0)) (Znth (i+1) choices 0) lj rj /\ ri < lj.

Definition Pre (trees : list (Z*Z)) : Prop := 1 <= Zlength trees <= 100000 /\
  Forall (fun p => 1 <= fst p <= 1000000000 /\ 1 <= snd p <= 1000000000) trees /\
  mono_inc (map fst trees).

Definition Spec (trees : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset Z.le (ValidFelling trees)
    (fun choices => Zlength (filter (fun x => negb (Z.eqb x 0)) choices)) out.
