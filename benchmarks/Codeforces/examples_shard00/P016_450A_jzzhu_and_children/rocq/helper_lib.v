
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition CandyTurns (m need : Z) : Z :=
  (need + m - 1) / m.

Definition LastMaxPrefix
    (m : Z) (wants : list Z)
    (processed best answer : Z) : Prop :=
  0 <= processed <= Zlength wants /\
  ((processed = 0 /\ best = 0 /\ answer = 1) \/
   (0 < processed /\
    1 <= answer <= processed /\
    best = CandyTurns m (Znth (answer - 1) wants 0) /\
    (forall j, 0 <= j < processed ->
       CandyTurns m (Znth j wants 0) <= best) /\
    (forall j, answer <= j < processed ->
       CandyTurns m (Znth j wants 0) < best))).
