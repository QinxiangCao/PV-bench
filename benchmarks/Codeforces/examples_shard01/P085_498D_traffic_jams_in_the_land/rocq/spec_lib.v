(* Codeforces 498/D - Traffic Jams in the Land: crossing segment i takes two
   minutes when the current time is a multiple of its period and one otherwise;
   answer ride-time queries interleaved with period updates. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One query (c, x, y): c = 'A' = 65 asks for the ride time from city x to city y,
   c = 'C' = 67 sets the period of segment x to y. *)
Definition TrafficQuery := (Z * Z * Z)%type.

(* Crossing one segment: two minutes when the moment of arrival is a multiple
   of that segment's period, one minute otherwise. *)
Definition CrossSegment (period times : list Z) (x i : Z) : Prop :=
  ((Znth (x + i - 1) period 2 | Znth i times 0) /\
   Znth (i + 1) times 0 = Znth i times 0 + 2) \/
  (~ (Znth (x + i - 1) period 2 | Znth i times 0) /\
   Znth (i + 1) times 0 = Znth i times 0 + 1).

(* The moments at which a ride leaving x at time zero reaches each crossing. *)
Definition RideTimes (period : list Z) (x y : Z) (times : list Z) : Prop :=
  Zlength times = y - x + 1 /\ Znth 0 times 0 = 0 /\
  forall i, 0 <= i < y - x -> CrossSegment period times x i.

(* How long the ride from x to y takes. *)
Definition RideTime (period : list Z) (x y t : Z) : Prop :=
  1 <= x < y /\ y <= Zlength period + 1 /\
  exists times : list Z, RideTimes period x y times /\ t = Znth (y - x) times 0.

(* How many of the first [i] queries ask for a ride time; it is also the
   position an answer takes in the printed list. *)
Definition AskCount (qs : list TrafficQuery) (i : Z) : Z :=
  #(fun j : Z => 0 <= j < i /\ let ' (d, _, _) := Znth j qs (0, 0, 0) in d = 65).

(* One query: 'C' resets a segment's period, 'A' leaves the road unchanged. *)
Definition QueryStep (qs : list TrafficQuery) (states : list (list Z)) (i : Z) : Prop :=
  let ' (c, x, y) := Znth i qs (0, 0, 0) in
  (c = 67 /\ Znth (i + 1) states [] = replace_Znth (x - 1) y (Znth i states [])) \/
  (c = 65 /\ Znth (i + 1) states [] = Znth i states []).

(* The whole run: the road after every query, and the answer each 'A' query
   contributes, in the order they are printed. *)
Definition TrafficTrace (init : list Z) (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z) : Prop :=
  Zlength states = Zlength qs + 1 /\ Znth 0 states [] = init /\
  Zlength answers = AskCount qs (Zlength qs) /\
  (forall i, 0 <= i < Zlength qs -> QueryStep qs states i) /\
  forall i, 0 <= i < Zlength qs -> let ' (c, x, y) := Znth i qs (0, 0, 0) in c = 65 ->
   exists t, RideTime (Znth i states []) x y t /\
     Znth (AskCount qs i) answers 0 = t.
Definition Pre (init : list Z) (qs : list TrafficQuery) : Prop :=
  (* Every clause below is stated explicitly in the P085 solver Require, which
     therefore omits the Pre(...) call.  The per-query clause is expanded there
     over the three parallel arrays the caller holds, which the Require ties to
     [qs] element by element:
       1 <= Zlength init <= 100000 /\
       Forall (fun x => 2 <= x <= 6) init /\
       1 <= Zlength qs <= 100000 /\
       Forall (fun q => let ' (c, x, y) := q in
         (c = 65 /\ 1 <= x < y /\ y <= Zlength init + 1) \/
         (c = 67 /\ 1 <= x <= Zlength init /\ 2 <= y <= 6)) qs. *)
  True.

(* out lists the answers to the 'A' queries in the order they are asked, taken
   along the run in which each 'C' query updates the road. *)
Definition Spec (init : list Z) (qs : list TrafficQuery) (out : list Z) : Prop :=
  exists states, TrafficTrace init qs states out.
