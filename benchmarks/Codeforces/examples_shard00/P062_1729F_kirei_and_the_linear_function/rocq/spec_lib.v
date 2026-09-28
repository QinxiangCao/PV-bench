Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DecimalSub (s : list Z) (l r : Z) : Z :=
  fold_left (fun v c => 10 * v + (c - 48)) (sublist l (r + 1) s) 0.

Definition QueryPair (s : list Z) (w : Z) (q : Z * Z * Z)
    (p : Z * Z) : Prop :=
  let '(l, r, k) := q in
  let '(x, y) := p in
  1 <= x /\ x + w - 1 <= Zlength s /\
  1 <= y /\ y + w - 1 <= Zlength s /\ x <> y /\
  (DecimalSub s (x - 1) (x + w - 2) * DecimalSub s (l - 1) (r - 1) +
    DecimalSub s (y - 1) (y + w - 2)) mod 9 = k.

Definition Pre (w : Z) (s : list Z) (qs : list (Z * Z * Z)) : Prop :=
  2 <= Zlength s <= 200000 /\ 1 <= w < Zlength s /\
  (* Character codes: decimal digits '0'..'9' = 48..57. *)
  Forall (fun c => 48 <= c <= 57) s.

Definition Spec (w : Z) (s : list Z) (qs : list (Z * Z * Z))
    (out : list (Z * Z)) : Prop :=
  Forall2 (fun q p =>
    (p = (-1, -1) /\
      (forall candidate, ~ QueryPair s w q candidate)) \/
    min_value_of_subset
      (fun left right : Z * Z =>
        fst left < fst right \/
        fst left = fst right /\ snd left <= snd right)
      (QueryPair s w q)
      (fun candidate => candidate) p) qs out.

(** Transparent projections for QCP's left-associated encoding of triples. *)
Definition ztriple_1 (p : Z * Z * Z) : Z := fst (fst p).

Definition ztriple_2 (p : Z * Z * Z) : Z := snd (fst p).

Definition ztriple_3 (p : Z * Z * Z) : Z := snd p.

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.Logic.Classical_Prop.

Require Import Coq.ZArith.Zquot.
