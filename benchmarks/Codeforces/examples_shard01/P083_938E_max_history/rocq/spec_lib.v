(* Codeforces 938/E - Max History: f of a permutation is what the running-record
   scan accumulates; sum f over all n! permutations, modulo 10^9+7. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One step of the scan: position i either beats the current record holder, who
   then pays their own value and hands the record over, or it does not and the
   position pays nothing. *)
Definition RecordStep (a order leaders add : list Z) (i : Z) : Prop :=
  (Znth (Znth (i - 1) leaders 1 - 1) a 0 < Znth (Znth i order 1 - 1) a 0 /\
   Znth i leaders 0 = Znth i order 1 /\
   Znth i add 0 = Znth (Znth (i - 1) leaders 1 - 1) a 0) \/
  (Znth (Znth (i - 1) leaders 1 - 1) a 0 >= Znth (Znth i order 1 - 1) a 0 /\
   Znth i leaders 0 = Znth (i - 1) leaders 0 /\
   Znth i add 0 = 0).

(* The scan over one permutation: [leaders] holds the record holder after each
   position and [add] what that position contributed. *)
Definition RecordRun (a order leaders add : list Z) : Prop :=
  Zlength leaders = Zlength a /\ Zlength add = Zlength a /\
  Znth 0 leaders 0 = Znth 0 order 1 /\ Znth 0 add 0 = 0 /\
  forall i, 1 <= i < Zlength a -> RecordStep a order leaders add i.

(* The value f of one permutation: everything the scan adds up. *)
Definition HistoryValue (a order : list Z) (v : Z) : Prop :=
  Permutation order (Zrange 1 (Zlength a + 1)) /\
  exists leaders add : list Z,
    RecordRun a order leaders add /\ v = fold_right Z.add 0 add.

(* ps lists every permutation of 1..n exactly once -- the n! orderings the sum
   ranges over. *)
Definition AllPermutations (n : Z) (ps : list (list Z)) : Prop :=
  NoDup ps /\ forall p, In p ps <-> (Permutation p (Zrange 1 (n + 1))).
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P083 solver Require, so dropped here:
       1 <= Zlength a <= 1000000 /\
       Forall (fun x => 1 <= x <= 1000000000) a  *)
  True.

(* out = (sum over all n! permutations p of HistoryValue(a, p)) mod (10^9 + 7). *)
Definition Spec (a : list Z) (out : Z) : Prop :=
  exists ps f, AllPermutations (Zlength a) ps /\ (forall p, In p ps -> HistoryValue a p (f p)) /\
  out = (fold_right Z.add 0) (map f ps) mod 1000000007.
