Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition AirportName (a : list Z) : Prop :=
  Zlength a = 3 /\ Forall (fun c => 65 <= c <= 90) a.

Definition ItineraryEndsAt
    (home : list Z) (flights : list (list Z * list Z)) (current : list Z) : Prop :=
  exists ordered locations,
    Permutation flights ordered /\
    Zlength locations = Zlength ordered + 1 /\
    Znth 0 locations [] = home /\
    (forall i, 0 <= i < Zlength ordered ->
       fst (Znth i ordered ([], [])) = Znth i locations [] /\
       snd (Znth i ordered ([], [])) = Znth (i + 1) locations []) /\
    Znth (Zlength locations - 1) locations [] = current.

Definition Pre (home : list Z) (flights : list (list Z * list Z)) : Prop :=
  AirportName home /\
  1 <= Zlength flights <= 100 /\
  Forall (fun f =>
    AirportName (fst f) /\ AirportName (snd f) /\
    ((fst f = home /\ snd f <> home) \/
     (fst f <> home /\ snd f = home))) flights /\
  exists current, ItineraryEndsAt home flights current.

Definition Spec
    (home : list Z) (flights : list (list Z * list Z)) (out : list Z) : Prop :=
  (out = [104; 111; 109; 101] /\ ItineraryEndsAt home flights home) \/
  (out = [99; 111; 110; 116; 101; 115; 116] /\
   exists current, current <> home /\ ItineraryEndsAt home flights current).
