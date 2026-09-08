Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.Znumtheory.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P082_623B_array_gcd.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition INF : Z := 4611686018427387904.

(* Minimum over a set of costs, falling back to the INF sentinel when no
   plan of the described kind exists.  This is exactly the shape the C
   program encodes with its INF guards. *)

Definition DPValue (S : Z -> Prop) (v : Z) : Prop :=
  min_value_of_subset_with_default Z.le S (fun x => x) INF v.

(* A plan that only looks at the first [i] entries of [a]: the segment
   [l, r) is removed, every surviving entry moves by at most one, and every
   surviving entry becomes divisible by [p].  [c] is what such a plan costs. *)

Definition PartialPlanCost (a : list Z) (del change p i l r c : Z) : Prop :=
  0 <= l /\ l <= r /\ r <= i /\ i <= Zlength a /\
  exists (delta result : list Z),
    Adjusted (sublist 0 l a ++ sublist r i a) delta result /\
    Forall (fun y => Z.divide p y) result /\
    c = ChangeCost del change l r delta.

(* The plans that are legal for the whole array and a fixed modulus [p]:
   the removed segment may not be the entire array. *)

Definition PFeasiblePlan (a : list Z) (del change p : Z) : Z -> Prop :=
  fun c => exists l r, r - l < Zlength a /\
             PartialPlanCost a del change p (Zlength a) l r c.

(* The cheapest such plan, or INF when [p] admits none. *)

Definition CostForPrime (a : list Z) (del change p out : Z) : Prop :=
  DPValue (PFeasiblePlan a del change p) out.

(* What one [add_factors] call appends: sound divisors, complete on primes,
   and few enough of them to stay inside the 256-cell scratch array. *)

Definition AddFactorsResult (v0 : Z) (fs : list Z) : Prop :=
  Forall (fun d => 2 <= d /\ Z.divide d v0) fs /\
  (forall q, prime q -> Z.divide q v0 -> In q fs) /\
  Zlength fs <= 30.

(* ------------------------------------------------------------------ *)
(* Internal predicates: they only describe states of the function      *)
(* bodies and never appear in a function contract.                     *)
(* ------------------------------------------------------------------ *)

(* Divisor bookkeeping shared by the three add_factors states. *)

Definition FactorsSoFar (v0 v : Z) (fs : list Z) : Prop :=
  1 <= v /\ Z.divide v v0 /\
  Forall (fun q => 2 <= q /\ Z.divide q v0) fs /\
  (forall q, prime q -> Z.divide q v0 -> Z.divide q v \/ In q fs).

(* Trial-division scan: nothing below d divides the remainder any more. *)

Definition AddFactorsScan (v0 v d : Z) (fs : list Z) : Prop :=
  FactorsSoFar v0 v fs /\
  (forall q, 2 <= q -> q < d -> ~ Z.divide q v) /\
  2 ^ (Zlength fs) * v <= v0.

(* Inside the division loop: d is already recorded but not yet divided out,
   so the doubling bound is one step weaker. *)

Definition AddFactorsExtract (v0 v d : Z) (fs : list Z) : Prop :=
  FactorsSoFar v0 v fs /\
  (forall q, 2 <= q -> q < d -> ~ Z.divide q v) /\
  2 <= d /\ In d fs /\
  2 ^ (Zlength fs - 1) * v <= v0.

(* After the scan the trial divisor is out of scope and the leftover is
   one or prime. *)

Definition AddFactorsResidual (v0 v : Z) (fs : list Z) : Prop :=
  FactorsSoFar v0 v fs /\
  (v = 1 \/ prime v) /\
  2 ^ (Zlength fs) * v <= v0.

(* Cheapest price of keeping one surviving element. *)

Definition ElemCost (change p x : Z) : Z :=
  if Z.eqb (x mod p) 0 then 0
  else if orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0) then change
  else INF.

(* The four families of partial plans tracked by the sweep. *)

Definition DPKeep (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => PartialPlanCost a del change p i i i c.

Definition DPCutFresh (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => PartialPlanCost a del change p i 0 i c.

Definition DPCutAfterKeep (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => exists l, 1 <= l /\ l < i /\ PartialPlanCost a del change p i l i c.

Definition DPAfter (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => exists l r, r < i /\ PartialPlanCost a del change p i l r c.

Definition CostForPrimeState
    (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z) : Prop :=
  DPValue (DPKeep a del change p i) keep /\
  DPValue (DPCutFresh a del change p i) cutFresh /\
  DPValue (DPCutAfterKeep a del change p i) cutAfterKeep /\
  DPValue (DPAfter a del change p i) after.

(* Soundness plus per-shift completeness of the collected moduli. *)

Definition CandidateCoverage (x y d : Z) (fs : list Z) : Prop :=
  Forall (fun q => 2 <= q) fs /\
  (forall q e, prime q -> -1 <= e -> e < d ->
     (Z.divide q (x + e) \/ Z.divide q (y + e)) -> In q fs).

(* Running minimum over the already examined moduli. *)

Definition BestPrefixCost
    (a : list Z) (del change : Z) (ps : list Z) (i best : Z) : Prop :=
  DPValue (fun c => exists j, 0 <= j < i /\ CostForPrime a del change (Znth j ps 0) c) best.
