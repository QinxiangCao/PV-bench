(* Codeforces 435/B - Pasha Maximizes: the largest number obtainable from a by at
   most k swaps of adjacent decimal digits. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

(* One move: exchange the digits at positions i and i + 1. *)
Definition AdjacentSwap (a b : list Z) : Prop :=
  exists i, 0 <= i < Zlength a - 1 /\
    b = replace_Znth (i + 1) (Znth i a 0) (replace_Znth i (Znth (i + 1) a 0) a).

(* b is reachable from a within k swaps: a chain of at most k adjacent swaps
   leads from a to b. *)
Definition SwapReach (a b : list Z) (k : Z) : Prop :=
  exists st : list (list Z), 1 <= Zlength st <= k + 1 /\ Znth 0 st [] = a /\
    Znth (Zlength st - 1) st [] = b /\
    forall i, 0 <= i < Zlength st - 1 -> AdjacentSwap (Znth i st []) (Znth (i + 1) st []).

(* The digits of a: 1 <= |digits| <= 19 since a <= 10^18, digits[0] <> 0, every
   digit in [0, 9]; and 0 <= k <= 100. *)
Definition Pre (digits : list Z) (k : Z) : Prop :=
  (* This legacy Pre is unused; the P039 solver Require states its byte-level
     input constraints directly.  The original clauses are preserved here:
       1 <= Zlength digits <= 19 /\ 0 <= k <= 100 /\
       Znth 0 digits 0 <> 0 /\ Forall (fun d => 0 <= d <= 9) digits. *)
  True.

(* out is reachable within k swaps, and every other reachable q satisfies
   q <= out lexicographically. All reachable strings have the same length, so
   this is the largest reachable number. *)
Definition Spec (digits : list Z) (k : Z) (out : list Z) : Prop :=
  SwapReach digits out k /\ forall q, SwapReach digits q k -> (q = out \/ ((exists i, 0 <= i < Z.min (Zlength q) (Zlength out) /\
    (forall j, 0 <= j < i -> Znth j q 0 = Znth j out 0) /\
    Znth i q 0 < Znth i out 0) \/
  (Zlength q < Zlength out /\ is_prefix q out))).
