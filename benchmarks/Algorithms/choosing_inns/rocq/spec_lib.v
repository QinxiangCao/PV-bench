Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition zrange (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).
Definition zrange_between (lo hi : Z) : list Z :=
  map (fun t => lo + Z.of_nat t) (seq 0 (Z.to_nat (hi - lo + 1))).
Definition affordable_betweenb (costs : list Z) (p lo hi : Z) : bool :=
  existsb (fun idx => Z.leb (Znth idx costs 0) p) (zrange_between lo hi).
Definition same_colorb (colors : list Z) (a b : Z) : bool :=
  Z.eqb (Znth a colors 0) (Znth b colors 0).
Definition choosing_pairb (colors costs : list Z) (p : Z) (pair : Z * Z) : bool :=
  let (left, right) := pair in
  same_colorb colors left right && affordable_betweenb costs p left right.
Definition choosing_pairs_up_to (n : Z) : list (Z * Z) :=
  flat_map (fun right => map (fun left => (left, right)) (zrange right))
           (zrange n).
Definition choosing_pair_count (colors costs : list Z) (p n : Z) : Z :=
  Z.of_nat
    (length
       (filter (choosing_pairb colors costs p) (choosing_pairs_up_to n))).
Definition ChoosingInputSafe
    (colors costs : list Z) (n k p : Z) : Prop :=
  0 <= n <= 200000 /\
  1 <= k <= 50 /\
  0 <= p <= 100 /\
  Zlength colors = n /\
  Zlength costs = n /\
  (forall idx, 0 <= idx < n -> 0 <= Znth idx colors 0 < k) /\
  (forall idx, 0 <= idx < n -> 0 <= Znth idx costs 0 <= 100).

(** Shape and arithmetic bounds for a concrete per-colour count array. *)
Definition ChoosingInnsAnswer
    (colors costs : list Z) (n k p answer : Z) : Prop :=
  answer = choosing_pair_count colors costs p n.

Require Import Coq.micromega.Psatz.
