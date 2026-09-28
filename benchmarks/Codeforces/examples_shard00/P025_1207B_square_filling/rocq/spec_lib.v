Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CellCovered (ops : list (Z * Z)) (row col : Z) : Prop :=
  exists x y,
    In (x, y) ops /\
    (row = x \/ row = x + 1) /\
    (col = y \/ col = y + 1).

Definition FillingOperations
    (n m : Z) (a : list (list Z)) (ops : list (Z * Z)) : Prop :=
  Zlength ops <= 2500 /\
  Forall (fun p => 0 <= fst p < n - 1 /\ 0 <= snd p < m - 1) ops /\
  forall i j, 0 <= i < n -> 0 <= j < m ->
    Znth j (Znth i a nil) 0 = 1 <-> CellCovered ops i j.

Definition Pre (n m : Z) (a : list (list Z)) : Prop :=
  2 <= n <= 50 /\ 2 <= m <= 50 /\
  Zlength a = n /\
  Forall (fun row => Zlength row = m /\
    Forall (fun cell => cell = 0 \/ cell = 1) row) a.

Definition Spec
    (n m : Z) (a : list (list Z)) (out : option (list (Z * Z))) : Prop :=
  (exists ops, out = Some ops /\ FillingOperations n m a ops) \/
  (out = None /\ forall ops, ~ FillingOperations n m a ops).

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.Logic.ClassicalEpsilon.
