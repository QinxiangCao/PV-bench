(* Codeforces 1765/E - Exchange: fewest quests -- each yielding one gold -- needed
   to reach n silver, given gold sells for a silver and costs b silver to buy. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One trade from state (g, x) = (gold, silver):
     g >= 1  and  (g, x) -> (g - 1, x + a)     sell one gold for a silver
     x >= b  and  (g, x) -> (g + 1, x - b)     buy one gold for b silver *)
Definition ExchangeStep (a b : Z) (s1 s2 : Z * Z) : Prop :=
  let ' (g, x) := s1 in let ' (g', x') := s2 in
  (g >= 1 /\ g' = g - 1 /\ x' = x + a) \/ (x >= b /\ g' = g + 1 /\ x' = x - b).

(* q quests suffice: some finite chain of exchange steps from the start state
   (q, 0) ends in a state (g, x) with g >= 0 and x >= n. *)
Definition ReachesSilver (n a b q : Z) : Prop :=
  exists states : list (Z * Z),
    states <> [] /\ Znth 0 states (0, 0) = (q, 0) /\
    (forall i, 0 <= i < Zlength states - 1 ->
       ExchangeStep a b (Znth i states (0, 0)) (Znth (i + 1) states (0, 0))) /\
    let ' (g, x) := Znth (Zlength states - 1) states (0, 0) in g >= 0 /\ x >= n.

(* 1 <= n <= 10^7 and 1 <= a, b <= 50. *)
Definition Pre (n a b : Z) : Prop :=
  (* Stated explicitly in the P014 solver Require, which therefore omits the
     Pre(...) call:
       1 <= n <= 10000000 /\ 1 <= a <= 50 /\ 1 <= b <= 50. *)
  True.

(* out = min { q >= 0 : ReachesSilver n a b q }. *)
Definition Spec (n a b out : Z) : Prop := min_value_of_subset Z.le (fun q => q >= 0 /\ ReachesSilver n a b q) (fun x => x) out.
