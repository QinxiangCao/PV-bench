(* Codeforces 2000/D - Right Left Wrong: repeatedly pick l < r with s_l = 'L' and
   s_r = 'R', score a_l + ... + a_r and erase that range; maximise the total. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope Z_scope.

(* Signature: solve_case(a s:list Z)->Z. A strip cell holds 'L' (76) or 'R' (82),
   and becomes '.' (46) once erased. *)

(* [st'] is [st] with every position in [l, r] replaced by '.'. *)
Definition Erased (st st' : list Z) (l r : Z) : Prop :=
  Zlength st' = Zlength st /\
  forall i, 0 <= i < Zlength st ->
    (l <= i <= r /\ Znth i st' 0 = 46) \/
    (~(l <= i <= r) /\ Znth i st' 0 = Znth i st 0).

(* One operation on a state of (remaining strip, score so far): pick l < r whose
   cells are still 'L' and 'R', add a_l + ... + a_r to the score, and erase the
   whole range. Erasing only removes those cells as future endpoints — an
   enclosing segment may still be chosen afterwards, and its sum counts the
   inner cells again. *)
Definition OpStep (a : list Z) (st st' : list Z * Z) : Prop :=
  exists l r,
    0 <= l < r /\ r < Zlength (fst st) /\
    Znth l (fst st) 0 = 76 /\ Znth r (fst st) 0 = 82 /\
    Erased (fst st) (fst st') l r /\
    snd st' = snd st + sum_range l r (fun i => Znth i a 0).

(* 2 <= |a| <= 200000, |s| = |a|, every a[i] in [1, 10^5], and every s[i] is
   'L' = 76 or 'R' = 82. *)
Definition Pre (a s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P026 solver Require, which
     therefore omits the Pre(...) call:
       2 <= Zlength a <= 200000 /\ Zlength s = Zlength a /\
       Forall (fun x => 1 <= x <= 100000) a /\
       Forall (fun c => c = 76 \/ c = 82) s. *)
  True.

(* The answer is the largest score reachable by any finite run of operations
   from the initial strip with score 0 (performing no operation is allowed, so
   0 is always attainable). *)
Definition Spec (a s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => exists st, clos_refl_trans (OpStep a) (s, 0) st /\ v = snd st)
    (fun x => x) out.
