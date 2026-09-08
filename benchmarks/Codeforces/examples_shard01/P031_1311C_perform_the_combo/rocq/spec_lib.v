(* Codeforces 1311/C - Perform the Combo: m failed tries stop after p_i characters
   and the last try completes s; count how often each letter is pressed. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* #{ i : 0 <= i < |xs| and xs[i] = x }, the occurrences of x in xs. *)
Definition Count (x : Z) (xs : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x).

Definition Pre (s tries : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P031 solver Require, which
     therefore omits the Pre(text, tries) call:
       2 <= Zlength s <= 200000 /\
       1 <= Zlength tries <= 200000 /\
       Forall (fun c => 97 <= c <= 122) s /\
       Forall (fun p => 1 <= p < Zlength s) tries. *)
  True.

(* |out| = 26, and for each letter c
     out[c - 97] = Count(c, s) + sum over tries p of Count(c, s[0..p))
   the final successful run plus the prefix typed during each failed try. *)
Definition Spec (s tries out : list Z) : Prop :=
  Zlength out = 26 /\
  forall c, 97 <= c <= 122 ->
    Znth (c - 97) out 0 =
      Count c s +
      (fold_right Z.add 0) (map (fun p => Count c (sublist 0 p s)) tries).
