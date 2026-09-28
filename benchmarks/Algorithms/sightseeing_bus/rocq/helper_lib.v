Require Export PVbench.Algorithms.sightseeing_bus.rocq.spec_lib.
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib MonotonicList.
From SumLib Require Import Sum ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition DestinationCounts
    (n m : Z) (destinations counts : list Z) : Prop :=
  Zlength counts = n /\
  forall station, 0 <= station < n ->
    Znth station counts 0 =
      sum (fun passenger =>
             0 <= passenger < m /\
             Znth passenger destinations 0 = station + 1)
          (fun _ => 1).

(* ------------------------------------------------------------------------- *)
(* Internal annotation states.  These declarations describe stable program
   points; array ownership, loop-index bounds, and [@pre] bridges stay in C. *)

Definition StationSummaryState
    (n m : Z) (times origins destinations latest counts : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts.

Definition WorkspacesZeroPrefix
    (latest counts : list Z) (processed : Z) : Prop :=
  Forall (fun x => x = 0) (sublist 0 processed latest) /\
  Forall (fun x => x = 0) (sublist 0 processed counts).


Definition LatestAtStationPrefix
    (m : Z) (times origins : list Z)
    (processed station latest : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun passenger =>
       0 <= passenger < processed /\
       passenger < m /\
       Znth passenger origins 0 = station + 1)
    (fun passenger => Znth passenger times 0)
    0 latest.

Definition PassengerAggregationPrefix
    (n m : Z) (times origins destinations : list Z)
    (processed : Z) (latest counts : list Z) : Prop :=
  (forall station, 0 <= station < n ->
     LatestAtStationPrefix
       m times origins processed station (Znth station latest 0)) /\
  (forall station, 0 <= station < n ->
     Znth station counts 0 =
       sum (fun passenger =>
              0 <= passenger < processed /\
              passenger < m /\
              Znth passenger destinations 0 = station + 1)
           (fun _ => 1)).

Definition ArrivalSimulationPrefix
    (n : Z) (dist latest arrivals : list Z)
    (processed next_arrival : Z) : Prop :=
  (forall station, 0 <= station < processed ->
     (station = 0 /\ Znth station arrivals 0 = 0) \/
     (0 < station /\
      exists departure,
        StationDeparture arrivals latest (station - 1) departure /\
        Znth station arrivals 0 =
          departure + Znth (station - 1) dist 0)) /\
  ((processed = 0 /\ next_arrival = 0) \/
   (0 < processed /\
    exists departure,
      StationDeparture arrivals latest (processed - 1) departure /\
      next_arrival =
        departure + Znth (processed - 1) dist 0)).

Definition MarginalBenefitScan
    (counts latest arrivals : list Z)
    (edge next_station benefit : Z) : Prop :=
  benefit =
    sum (fun station => edge + 1 <= station < next_station)
        (fun station => Znth station counts 0) /\
  Forall2 Z.lt
    (map (fun station => Znth station latest 0) (Zrange (edge + 1) next_station))
    (map (fun station => Znth station arrivals 0) (Zrange (edge + 1) next_station)).


Definition EdgeMarginalBenefit
    (n : Z) (counts latest arrivals : list Z)
    (edge benefit : Z) : Prop :=
  exists stop,
    edge + 2 <= stop <= n /\
    Forall2 Z.lt
      (map (fun station => Znth station latest 0) (Zrange (edge + 1) (stop - 1)))
      (map (fun station => Znth station arrivals 0) (Zrange (edge + 1) (stop - 1))) /\
    (stop = n \/
     Znth (stop - 1) arrivals 0 <= Znth (stop - 1) latest 0) /\
    benefit =
      sum (fun station => edge + 1 <= station < stop)
          (fun station => Znth station counts 0).

Definition EligibleEdgeBenefit
    (n : Z) (dist counts latest arrivals : list Z)
    (scanned : Z) (choice : Z * Z) : Prop :=
  let '(edge, benefit) := choice in
  0 <= edge < scanned /\
  edge < n - 1 /\
  0 < Znth edge dist 0 /\
  EdgeMarginalBenefit n counts latest arrivals edge benefit.

Definition EdgeChoicePrefix
    (n : Z) (dist counts latest arrivals : list Z)
    (scanned best position : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (EligibleEdgeBenefit n dist counts latest arrivals scanned)
    (fun choice => snd choice) 0 best /\
  ((best = 0 /\ position = -1) \/
   EligibleEdgeBenefit
     n dist counts latest arrivals scanned (position, best)).

Definition BestBoostChoice
    (n : Z) (dist counts latest arrivals : list Z)
    (best position : Z) : Prop :=
  EdgeChoicePrefix
    n dist counts latest arrivals (n - 1) best position.

Definition ArrivalRepairProgress
    (n : Z)
    (old_dist old_arrivals new_dist new_arrivals latest : list Z)
    (edge next_station : Z) : Prop :=
  (forall candidate_edge, 0 <= candidate_edge < n - 1 ->
     Znth candidate_edge new_dist 0 =
       if Z.eq_dec candidate_edge edge
       then Znth candidate_edge old_dist 0 - 1
       else Znth candidate_edge old_dist 0) /\
  Forall2 eq
    (map (fun station => Znth station new_arrivals 0) (Zrange 0 (edge + 1)))
    (map (fun station => Znth station old_arrivals 0) (Zrange 0 (edge + 1))) /\
  Forall2 (fun current previous =>
      current = fst previous - 1 /\ snd previous <= current)
    (map (fun station => Znth station new_arrivals 0) (Zrange (edge + 1) next_station))
    (map (fun station => (Znth station old_arrivals 0, Znth station latest 0))
      (Zrange (edge + 1) next_station)) /\
  Forall2 eq
    (map (fun station => Znth station new_arrivals 0) (Zrange next_station n))
    (map (fun station => Znth station old_arrivals 0) (Zrange next_station n)).

Definition BoosterProgress
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts /\
  FeasibleBoostedDistances
    n (budget - remaining) initial_dist dist /\
  BusArrivalSchedule n dist latest arrivals /\
  exists current_total,
    PassengerTravelTotal
      m times destinations arrivals current_total /\
    SightseeingMinimumTotal
      n m (budget - remaining)
      initial_dist times origins destinations current_total.

Definition OptimizedBusState
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts /\
  FeasibleBoostedDistances n budget initial_dist dist /\
  BusArrivalSchedule n dist latest arrivals /\
  exists optimum,
    PassengerTravelTotal m times destinations arrivals optimum /\
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations optimum.

Definition TravelSumPrefix
    (m : Z) (times destinations arrivals : list Z)
    (processed total : Z) : Prop :=
  total =
    sum (fun passenger => 0 <= passenger < processed /\ passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0 -
           Znth passenger times 0).
