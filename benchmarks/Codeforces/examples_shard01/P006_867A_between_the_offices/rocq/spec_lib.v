(* Codeforces 867/A - Between the Offices: given the day-by-day city sequence,
   decide whether Seattle -> San Francisco flights outnumber the reverse. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Overnight flights from city 'from' to city 'to':
     #{ i : 0 <= i <= |days| - 2,  days[i] = from and days[i+1] = to } *)
Definition TransitionCount (days : list Z) (from to : Z) : Z :=
  sum_range 0 (Zlength days - 2)
    (fun i =>
       if (Z.eqb (Znth i days 0) from &&
           Z.eqb (Znth (i + 1) days 0) to)%bool
       then 1
       else 0).

(* 2 <= |days| <= 100, each entry 'S' = 83 (Seattle) or 'F' = 70 (San Francisco). *)
Definition Pre (days : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P006 solver Require, which
     therefore omits the Pre(...) call:
       2 <= Zlength days <= 100 /\
       Forall (fun c => c = 83 \/ c = 70) days. *)
  True.

(* out = true exactly when S -> F flights strictly outnumber F -> S ones; ties
   and the reverse case print NO. *)
Definition Spec (days : list Z) (out : bool) : Prop :=
  (out = true /\ TransitionCount days 83 70 >
                 TransitionCount days 70 83) \/
  (out = false /\ TransitionCount days 83 70 <=
                  TransitionCount days 70 83).

(* Shared yes/no vocabulary: verdict true prints 1, false prints 0. *)
Definition VerdictCode (answer : bool) (code : Z) : Prop :=
  (answer = true /\ code = 1) \/
  (answer = false /\ code = 0).
