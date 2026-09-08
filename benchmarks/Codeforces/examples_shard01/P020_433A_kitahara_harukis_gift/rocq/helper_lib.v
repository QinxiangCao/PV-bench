Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The executable program measures weight in units of 100 grams.  These
   predicates describe the mathematical meaning of its running total and of
   the finite reachability table; they do not prescribe an implementation. *)
Definition UnitWeight (x : Z) : Z := x / 100.

Definition UnitSum (w : list Z) : Z :=
  fold_right Z.add 0 (map UnitWeight w).

Definition PrefixUnitTotal (w : list Z) (i total : Z) : Prop :=
  0 <= i <= Zlength w /\
  total = UnitSum (sublist 0 i w).

Definition UnitSelectableSum (w : list Z) (target : Z) : Prop :=
  exists chosen : list Z,
    Zlength chosen = Zlength w /\
    Forall (fun b => b = 0 \/ b = 1) chosen /\
    target =
      fold_right Z.add 0
        (map (fun q => fst q * UnitWeight (snd q)) (combine chosen w)).

Definition ReachTable
    (w : list Z) (i total : Z) (table : list Z) : Prop :=
  Zlength table = 205 /\
  (forall k, 0 <= k < 205 -> Znth k table 0 = 0 \/ Znth k table 0 = 1) /\
  forall k, 0 <= k <= total ->
    (Znth k table 0 <> 0 <->
     UnitSelectableSum (sublist 0 i w) k).

Definition ReachInnerProgress
    (w : list Z) (i s total : Z) (table : list Z) : Prop :=
  Zlength table = 205 /\
  (forall k, 0 <= k < 205 -> Znth k table 0 = 0 \/ Znth k table 0 = 1) /\
  (forall k, 0 <= k <= total -> s < k ->
    (Znth k table 0 <> 0 <->
     UnitSelectableSum (sublist 0 (i + 1) w) k)) /\
  forall k, 0 <= k <= total -> k <= s ->
    (Znth k table 0 <> 0 <->
     UnitSelectableSum (sublist 0 i w) k).
