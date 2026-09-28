From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib MonotonicList.
From SumLib Require Import Sum ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

(* The latest passenger-arrival time at a station is expressed through the
   project MaxMin library.  The default 0 covers stations with no passengers. *)
Definition LatestAtStation
    (m : Z) (times origins : list Z) (station latest : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun passenger =>
       0 <= passenger < m /\
       Znth passenger origins 0 = station + 1)
    (fun passenger => Znth passenger times 0)
    0 latest.

Definition LatestDepartures
    (n m : Z) (times origins latest : list Z) : Prop :=
  Zlength latest = n /\
  forall station, 0 <= station < n ->
    LatestAtStation m times origins station (Znth station latest 0).

Definition FeasibleBoostedDistances
    (n budget : Z) (initial_dist final_dist : list Z) : Prop :=
  Zlength final_dist = n - 1 /\
  Forall2 (fun final initial => 0 <= final <= initial)
    (map (fun edge => Znth edge final_dist 0) (Zrange 0 (n - 1)))
    (map (fun edge => Znth edge initial_dist 0) (Zrange 0 (n - 1))) /\
  sum (fun edge => 0 <= edge < n - 1)
      (fun edge =>
         Znth edge initial_dist 0 - Znth edge final_dist 0) <= budget.

(* A departure is the larger of the bus-arrival time and the latest passenger
   arrival time.  This maximum is deliberately represented by MaxMinLib. *)
Definition StationDeparture
    (arrivals latest : list Z) (station departure : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate => candidate = Znth station latest 0)
    (fun candidate => candidate)
    (Znth station arrivals 0) departure.

Definition BusArrivalSchedule
    (n : Z) (dist latest arrivals : list Z) : Prop :=
  Zlength arrivals = n /\
  Znth 0 arrivals 0 = 0 /\
  forall station, 0 <= station < n - 1 ->
    exists departure,
      StationDeparture arrivals latest station departure /\
      Znth (station + 1) arrivals 0 =
        departure + Znth station dist 0.

Definition PassengerTravelTotal
    (m : Z) (times destinations arrivals : list Z) (total : Z) : Prop :=
  total =
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0 -
           Znth passenger times 0).

Definition SightseeingCandidateTotal
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (total : Z) : Prop :=
  exists final_dist latest arrivals,
    LatestDepartures n m times origins latest /\
    FeasibleBoostedDistances n budget initial_dist final_dist /\
    BusArrivalSchedule n final_dist latest arrivals /\
    PassengerTravelTotal m times destinations arrivals total.

Definition SightseeingMinimumTotal
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (SightseeingCandidateTotal
       n m budget initial_dist times origins destinations)
    (fun total => total) answer.
