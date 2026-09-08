(* Codeforces 1436/F - Sum Over Subsets: over all pairs B subset A of the multiset
   S with |B| = |A| - 1 and gcd(A) = 1, sum (sum of A) * (sum of B), modulo
   998244353. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* d = gcd(xs) for a non-empty xs, and d > 0. *)
Definition IsPositiveGcd (d : Z) (xs : list Z) : Prop :=
  d > 0 /\ xs <> [] /\ d = fold_right Z.gcd 0 xs.

(* s is the multiset S written out element by element: |s| = sum(freq), every
   entry is one of vals, and vals[i] occurs exactly freq[i] times. *)
Definition ExpandedMultiset (vals freq : list Z) (s : list Z) : Prop :=
  Zlength s = (fold_right Z.add 0) freq /\
  Forall (fun x => In x vals) s /\
  forall i, 0 <= i < Zlength vals ->
    (#(fun j : Z => 0 <= j < Zlength s /\ Znth j s 0 = (Znth i vals 0))) = Znth i freq 0.

(* (A, B), given as 0/1 indicator vectors over s, is a counted pair:
     B[i] <= A[i] for every i                B is a subset of A
     sum(B) = sum(A) - 1                     |B| = |A| - 1
     gcd of the elements A selects is 1
     term = (sum of A's elements) * (sum of B's elements) *)
Definition ValidSubsetPair (s : list Z) (ab : list Z * list Z) (term : Z) : Prop :=
  let ' (A, B) := ab in Zlength A = Zlength s /\ Zlength B = Zlength s /\
  Forall (fun x => x = 0 \/ x = 1) A /\ Forall (fun x => x = 0 \/ x = 1) B /\
  (forall i, 0 <= i < Zlength s -> Znth i B 0 <= Znth i A 0) /\
  (fold_right Z.add 0) B = (fold_right Z.add 0) A - 1 /\
  (exists g, IsPositiveGcd g (map snd (filter (fun q => Z.eqb (fst q) 1) (combine A s))) /\ g = 1) /\
  term = (fold_right Z.add 0) (map snd (filter (fun q => Z.eqb (fst q) 1) (combine A s))) *
          (fold_right Z.add 0) (map snd (filter (fun q => Z.eqb (fst q) 1) (combine B s))).

(* ps lists every counted pair exactly once. *)
Definition AllSubsetPairs (s : list Z) (ps : list (list Z * list Z)) : Prop :=
  NoDup ps /\ forall q, In q ps <-> exists term, ValidSubsetPair s q term.

(* The largest value the input mentions; main seeds its running maximum with 1. *)
Definition maximum_value (vals : list Z) : Z :=
  fold_right Z.max 1 vals.

(* How the three per-value tables main hands to the solver represent the input:
   the total frequency of each value and its first and second moments. *)
Definition aggregate_arrays (vals freq cnts sums squares : list Z) (maxv : Z) : Prop :=
  Zlength cnts = maxv + 1 /\ Zlength sums = maxv + 1 /\ Zlength squares = maxv + 1 /\
  (forall i, 0 <= i < Zlength vals ->
     Znth (Znth i vals 0) cnts 0 = Znth i freq 0 /\
     Znth (Znth i vals 0) sums 0 =
       (Znth i vals 0 * Znth i freq 0) mod 998244353 /\
     Znth (Znth i vals 0) squares 0 =
       (Znth i vals 0 * Znth i vals 0 * Znth i freq 0) mod 998244353) /\
  (forall v, 0 <= v <= maxv -> ~ In v vals ->
     Znth v cnts 0 = 0 /\ Znth v sums 0 = 0 /\ Znth v squares 0 = 0).

Definition Pre (vals freq : list Z) : Prop :=
  (* Stated explicitly in the P096 solver Require, so dropped here:
       1 <= Zlength vals <= 100000 /\
       Zlength freq = Zlength vals /\
       Forall (fun x => 1 <= x <= 100000) vals /\
       Forall (fun x => 1 <= x <= 1000000000) freq  *)
  NoDup vals.

(* out = (sum of term over all counted pairs) mod 998244353. *)
Definition Spec (vals freq : list Z) (out : Z) : Prop :=
  exists s ps f, ExpandedMultiset vals freq s /\ AllSubsetPairs s ps /\
   (forall q, In q ps -> ValidSubsetPair s q (f q)) /\ out = (fold_right Z.add 0) (map f ps) mod 998244353.
