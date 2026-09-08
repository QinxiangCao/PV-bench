(* Codeforces 602/A - Two Bases: compare X, written in base bx, with Y, written in
   base by. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Value of a positional numeral, digits most-significant first: the Horner fold
   acc * base + d gives sum over i of digits[i] * base^(|digits| - 1 - i). *)
Definition numeral (base : Z) (digits : list Z) : Z :=
  fold_left (fun acc d => acc * base + d) digits 0.

(* The base, digit-count, and digit-range bounds are stated explicitly in the
   solver Require.  Pre retains bx <> basey and the no-leading-zero conditions. *)
Definition Pre (bx basey : Z) (x y : list Z) : Prop :=
  (* 2 <= bx <= 40 /\ *)
  (* 2 <= basey <= 40 /\ *)
  bx <> basey /\
  (* 1 <= Zlength x <= 10 /\ 1 <= Zlength y <= 10 /\ *)
  Znth 0 x 0 <> 0 /\ Znth 0 y 0 <> 0
  (* /\Forall (fun d => 0 <= d < bx) x /\ Forall (fun d => 0 <= d < basey) y *)
  .

(* out is the character code printed:
     60 = '<'   when X < Y
     62 = '>'   when X > Y
     61 = '='   when X = Y *)
Definition Spec (bx basey : Z) (x y : list Z) (out : Z) : Prop :=
  (out = 60 /\ numeral bx x < numeral basey y) \/
  (out = 62 /\ numeral bx x > numeral basey y) \/
  (out = 61 /\ numeral bx x = numeral basey y).
