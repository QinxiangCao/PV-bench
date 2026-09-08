(* Codeforces 847/H - Load Testing: fewest requests to add so the load strictly
   increases up to some minute and strictly decreases after it. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* a strictly increases up to some peak and strictly decreases after it:
     a[i] < a[i+1] for i < peak
     a[i] > a[i+1] for peak <= i < |a| - 1
   Either side may be empty; equal neighbours are never allowed. *)
Definition Mountain (a : list Z) : Prop :=
  exists peak, 0 <= peak < Zlength a /\
    (forall i, 0 <= i < peak -> Znth i a 0 < Znth (i + 1) a 0) /\
    (forall i, peak <= i < Zlength a - 1 -> Znth i a 0 > Znth (i + 1) a 0).

(* cost extra requests suffice: some b is pointwise at least a, is a mountain, and
   has sum(b) - sum(a) = cost -- requests are only ever added. *)
Definition AddedLoad (a : list Z) (cost : Z) : Prop :=
  exists b, Zlength b = Zlength a /\
    (forall i, 0 <= i < Zlength a -> Znth i a 0 <= Znth i b 0) /\ Mountain b /\
    cost = (fold_right Z.add 0) b - (fold_right Z.add 0) a.
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P050 solver Require, so dropped here:
       1 <= Zlength a <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) a  *)
  True.

(* out = min { cost : AddedLoad a cost }. *)
Definition Spec (a : list Z) (out : Z) : Prop := min_value_of_subset Z.le (AddedLoad a) (fun x => x) out.
