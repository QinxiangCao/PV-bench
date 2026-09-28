Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CandyTaken (sweet : Z -> Prop) (friend remaining taken : Z) : Prop :=
  (sweet friend /\ ((remaining >= 2 /\ taken = 2) \/ (remaining = 1 /\ taken = 1))) \/
  (~ sweet friend /\ remaining >= 1 /\ taken = 1).

Definition CandyObservation (n l r k : Z) (sweet : Z -> Prop) : Prop :=
  (forall p, sweet p -> 1 <= p <= n) /\
  exists friends remaining taken steps,
    Zlength friends = steps /\ Zlength remaining = steps + 1 /\
    Zlength taken = steps /\ Znth 0 friends 0 = l /\ Znth 0 remaining 0 = k /\
    (forall i, 0 <= i < steps ->
      CandyTaken sweet (Znth i friends 0) (Znth i remaining 0) (Znth i taken 0) /\
      Znth (i+1) remaining 0 = Znth i remaining 0 - Znth i taken 0 /\
      (i+1 < steps -> Znth (i+1) friends 0 = 1 + (Znth i friends 0 mod n))) /\
    Znth (steps-1) friends 0 = r /\ Znth steps remaining 0 = 0.

Definition Pre (n l r k : Z) : Prop :=
  1 <= n <= 100000000000 /\ 1 <= k <= 100000000000 /\
  1 <= l <= n /\ 1 <= r <= n.

Definition Spec (n l r k out : Z) : Prop :=
  (out = -1 /\ forall sweet, ~ CandyObservation n l r k sweet) \/
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      CandyObservation n l r k (fst candidate) /\
      snd candidate = #(fun p : Z => 1 <= p < n + 1 /\ fst candidate p))
    snd out.

Require Import Coq.micromega.Lia.

Require Import Coq.Sorting.Permutation.

Require Import Coq.micromega.Psatz.
