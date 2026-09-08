(* Codeforces 1266/C - Diverse Matrix: build an r x c matrix whose r row gcds and
   c column gcds are pairwise distinct and whose largest gcd is as small as
   possible, or report that none exists. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* d = gcd(xs) for a non-empty xs, and d > 0. *)
Definition IsPositiveGcd (d : Z) (xs : list Z) : Prop :=
  d > 0 /\ xs <> [] /\ d = fold_right Z.gcd 0 xs.

(* The array b the statement builds from a matrix: the greatest common divisor
   of each row, and after them the greatest common divisor of each column. *)
Definition GcdArray (r c : Z) (g : list (list Z)) (b : list Z) : Prop :=
  Zlength b = r + c /\
  (forall i, 0 <= i < r -> IsPositiveGcd (Znth i b 0) (Znth i g [])) /\
  (forall j, 0 <= j < c ->
     IsPositiveGcd (Znth (r + j) b 0) (map (fun row => Znth j row 0) g)).

(* A matrix is diverse when those r + c divisors are pairwise distinct.  Its
   entries are the positive integers the output format allows. *)
Definition DiverseMatrix (r c : Z) (g : list (list Z)) : Prop :=
  Zlength g = r /\
  Forall (fun row => Zlength row = c) g /\
  Forall (Forall (fun x => 1 <= x <= 1000000000)) g /\
  exists b : list Z, GcdArray r c g b /\ NoDup b.

(* The magnitude of a matrix: the largest of those divisors. *)
Definition Magnitude (r c : Z) (g : list (list Z)) (mag : Z) : Prop :=
  exists b : list Z, GcdArray r c g b /\
    max_value_of_subset Z.le (fun x => In x b) (fun x => x) mag.

Definition Pre (r c : Z) : Prop :=
  (* Every clause below is stated explicitly in the P037 solver Require, which
     therefore omits the Pre(...) call:
       1 <= r <= 500 /\ 1 <= c <= 500. *)
  True.

(* Print a diverse matrix of least magnitude, or nothing at all when no diverse
   matrix of that shape exists. *)
Definition Spec (r c : Z) (out : option (list (list Z))) : Prop :=
  (out = None /\ ~ exists g, DiverseMatrix r c g) \/
  (exists (g : list (list Z)) (mag : Z),
     out = Some g /\ DiverseMatrix r c g /\ Magnitude r c g mag /\
     min_value_of_subset Z.le
       (fun m' => exists g', DiverseMatrix r c g' /\ Magnitude r c g' m')
       (fun x => x) mag).
