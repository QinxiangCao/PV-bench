(* Codeforces 1243/B2 - Character Swap (Hard Version): make the two distinct
   strings equal using at most 2n swaps of s_i with t_j, printing the swaps, or
   report that it is impossible. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One operation: op = (i, j) exchanges s[i] with t[j]. *)
Definition CrossSwap (st st' : list Z * list Z) (op : Z * Z) : Prop :=
  let ' (s, t) := st in let ' (s', t') := st' in let ' (i, j) := op in
  0 <= i < Zlength s /\ 0 <= j < Zlength t /\
  s' = replace_Znth i (Znth j t 0) s /\ t' = replace_Znth j (Znth i s 0) t.

(* ops is a valid solution:
     1 <= |ops| <= 2 * |s|                    the operation budget
     applying ops in order from (s, t) ...
     ... ends with the two strings equal *)
Definition SwapsWork (s t : list Z) (ops : list (Z * Z)) : Prop :=
  1 <= Zlength ops <= 2 * Zlength s /\ exists st : list (list Z * list Z),
    Zlength st = Zlength ops + 1 /\ Znth 0 st ([], []) = (s, t) /\
    (forall q, 0 <= q < Zlength ops -> CrossSwap (Znth q st ([], [])) (Znth (q + 1) st ([], [])) (Znth q ops (0, 0))) /\
    fst (Znth (Zlength ops) st ([], [])) = snd (Znth (Zlength ops) st ([], [])).
Definition Pre (s t : list Z) : Prop :=
  (* Stated explicitly in the P046 solver Require, so dropped here:
       2 <= Zlength s <= 50 /\
       Zlength t = Zlength s /\
       Forall (fun c => 97 <= c <= 122) s /\
       Forall (fun c => 97 <= c <= 122) t  *)
  s <> t.

(* out = None      no such sequence exists, so No is printed
   out = Some ops  ops works; any working sequence is accepted, none minimised *)
Definition Spec (s t : list Z) (out : option (list (Z * Z))) : Prop :=
  (out = None /\ ~exists ops, SwapsWork s t ops) \/ (exists ops, out = Some ops /\ SwapsWork s t ops).
