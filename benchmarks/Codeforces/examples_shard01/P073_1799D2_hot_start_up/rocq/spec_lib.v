(* Codeforces 1799/D2 - Hot Start Up (hard version): run the programs in order on
   two CPUs, a program costing hot time when it repeats on the same CPU and cold
   time otherwise; minimise the total. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Position i runs a program that already ran on the same cpu, and j is that
   previous run: no position between them used that cpu. *)
Definition HotStart (prog cpu : list Z) (i j : Z) : Prop :=
  0 <= j < i /\ Znth j cpu 0 = Znth i cpu 0 /\
  (forall q, j < q < i -> Znth q cpu 0 <> Znth i cpu 0) /\
  Znth j prog 0 = Znth i prog 0.

(* What position i costs: the hot time after such a previous run, the cold time
   otherwise. *)
Definition RunTime (prog cold hot cpu times : list Z) (i : Z) : Prop :=
  (exists j, HotStart prog cpu i j /\
     Znth i times 0 = Znth (Znth i prog 0 - 1) hot 0) \/
  ((~ exists j, HotStart prog cpu i j) /\
   Znth i times 0 = Znth (Znth i prog 0 - 1) cold 0).

(* times is the per-position cost vector of the schedule cpu: |times| = |prog| and
   each times[i] is the RunTime of position i. *)
Definition RunTimes (prog cold hot cpu times : list Z) : Prop :=
  Zlength times = Zlength prog /\
  forall i, 0 <= i < Zlength prog -> RunTime prog cold hot cpu times i.

(* Every program is run on one of the two cpus, in the given order. *)
Definition ValidSchedule (prog cpu : list Z) : Prop :=
  Zlength cpu = Zlength prog /\ Forall (fun x => x = 1 \/ x = 2) cpu.

(* cost is the total time of a valid schedule cpu: the sum of its per-position
   run times. *)
Definition RunCost (prog cold hot cpu : list Z) (cost : Z) : Prop :=
  ValidSchedule prog cpu /\
  exists times, RunTimes prog cold hot cpu times /\
    cost = fold_right Z.add 0 times.
Definition Pre (prog cold hot : list Z) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= Zlength prog <= 300000 /\
       1 <= Zlength cold <= 300000 /\
       Zlength hot = Zlength cold /\
       Forall (fun x => 1 <= x <= Zlength cold) prog /\
       forall i, 0 <= i < Zlength cold ->
         1 <= Znth i hot 0 <= Znth i cold 0 /\
         Znth i cold 0 <= 1000000000. *)
  True.

(* out = min { cost : some schedule cpu costs that much }. *)
Definition Spec (prog cold hot : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists cpu, RunCost prog cold hot cpu v) (fun x => x) out.
