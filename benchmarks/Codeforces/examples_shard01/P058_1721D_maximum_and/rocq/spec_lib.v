(* Codeforces 1721/D - Maximum AND: reorder b to maximise the bitwise AND of all
   the a_i xor b_i. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Bitwise AND of xs over 30-bit values; the empty list gives the all-ones mask
   2^30 - 1, the neutral element. *)
Definition AndList30 (xs : list Z) : Z := fold_right Z.land (Z.pow 2 30 - 1) xs.

(* v is attainable: for some permutation p of b,
     v = (a[0] xor p[0]) and (a[1] xor p[1]) and ... and (a[n-1] xor p[n-1]) *)
Definition AndCandidate (a b : list Z) (v : Z) : Prop :=
  exists p, Permutation p b /\ v = AndList30 (map (fun q => Z.lxor (fst q) (snd q)) (combine a p)).

(* Every entry of a and b lies in [0, 2^30); the length bounds are stated in the
   solver Require instead, so they are commented out here. *)
Definition Pre (a b : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P058 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 100000 /\
       Zlength b = Zlength a /\
       Forall (fun x => 0 <= x < Z.pow 2 30) a /\
       Forall (fun x => 0 <= x < Z.pow 2 30) b. *)
  True.

(* out = max { v : AndCandidate a b v }. *)
Definition Spec (a b : list Z) (out : Z) : Prop := max_value_of_subset Z.le (AndCandidate a b) (fun x => x) out.
