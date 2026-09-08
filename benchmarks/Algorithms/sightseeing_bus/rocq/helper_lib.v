Require Import PVbench.Algorithms.sightseeing_bus.rocq.spec_lib.

From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SumLib Require Import Sum ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition StationSummaryState
    (n m : Z) (times origins destinations latest counts : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts.
Definition CanonicalBusState
    (n m : Z)
    (times origins destinations dist latest counts arrivals : list Z) : Prop :=
  StationSummaryState n m times origins destinations latest counts /\
  BusArrivalSchedule n dist latest arrivals.
Definition WorkspacesZeroPrefix
    (latest counts : list Z) (processed : Z) : Prop :=
  forall station, 0 <= station < processed ->
    Znth station latest 0 = 0 /\ Znth station counts 0 = 0.
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
  forall station, edge + 1 <= station < next_station ->
    Znth station latest 0 < Znth station arrivals 0.
Definition EdgeMarginalBenefit
    (n : Z) (counts latest arrivals : list Z)
    (edge benefit : Z) : Prop :=
  exists stop,
    edge + 2 <= stop <= n /\
    (forall station, edge + 1 <= station < stop - 1 ->
       Znth station latest 0 < Znth station arrivals 0) /\
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
  (forall station, 0 <= station <= edge ->
     Znth station new_arrivals 0 = Znth station old_arrivals 0) /\
  (forall station, edge < station < next_station ->
     Znth station new_arrivals 0 = Znth station old_arrivals 0 - 1 /\
     Znth station latest 0 <= Znth station new_arrivals 0) /\
  (forall station, next_station <= station < n ->
     Znth station new_arrivals 0 = Znth station old_arrivals 0).
Definition ArrivalRepairOutcome
    (n : Z)
    (old_dist old_arrivals new_dist new_arrivals latest : list Z)
    (edge : Z) : Prop :=
  exists stop,
    edge + 1 <= stop <= n /\
    (forall candidate_edge, 0 <= candidate_edge < n - 1 ->
       Znth candidate_edge new_dist 0 =
         if Z.eq_dec candidate_edge edge
         then Znth candidate_edge old_dist 0 - 1
         else Znth candidate_edge old_dist 0) /\
    (forall station, 0 <= station <= edge ->
       Znth station new_arrivals 0 = Znth station old_arrivals 0) /\
    (forall station, edge < station < stop ->
       Znth station new_arrivals 0 = Znth station old_arrivals 0 - 1 /\
       Znth station latest 0 <= Znth station new_arrivals 0) /\
    ((stop = n /\
      forall station, edge < station < n ->
        Znth station new_arrivals 0 = Znth station old_arrivals 0 - 1) \/
     (stop < n /\
      Znth stop new_arrivals 0 = Znth stop old_arrivals 0 - 1 /\
      Znth stop new_arrivals 0 < Znth stop latest 0 /\
      forall station, stop < station < n ->
        Znth station new_arrivals 0 = Znth station old_arrivals 0)).
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
      initial_dist times origins destinations current_total /\
    0 <= current_total <= 2000000000.
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
      n m budget initial_dist times origins destinations optimum /\
    0 <= optimum <= 2000000000.
Definition TravelSumPrefix
    (m : Z) (times destinations arrivals : list Z)
    (processed total : Z) : Prop :=
  total =
    sum (fun passenger => 0 <= passenger < processed /\ passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0 -
           Znth passenger times 0).

(* ------------------------------------------------------------------------- *)
(* Chain-schedule primal/dual certificate.  This is a mathematical proof
   interface, not a mirror of the C control flow. *)
Definition ChainDualCertificate
    (n budget : Z) (initial_dist latest counts : list Z)
    (alpha beta delta : list Z) (gamma lower : Z) : Prop :=
  Zlength alpha = n - 1 /\
  Zlength beta = n - 1 /\
  Zlength delta = n - 1 /\
  0 <= gamma /\
  (forall edge, 0 <= edge < n - 1 ->
     0 <= Znth edge alpha 0 /\
     0 <= Znth edge beta 0 /\
     0 <= Znth edge delta 0 /\
     Znth edge alpha 0 + Znth edge beta 0 <=
       gamma + Znth edge delta 0) /\
  (forall station, 1 <= station < n - 1 ->
     Znth (station - 1) alpha 0 + Znth (station - 1) beta 0 -
       Znth station alpha 0 <= Znth station counts 0) /\
  (Znth (n - 2) alpha 0 + Znth (n - 2) beta 0 <=
     Znth (n - 1) counts 0) /\
  lower =
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 *
             (Znth edge alpha 0 + Znth edge beta 0) +
           Znth edge latest 0 * Znth edge beta 0 -
           Znth edge initial_dist 0 * Znth edge delta 0) -
    budget * gamma.
Definition SightseeingDualLowerBound
    (n m budget : Z)
    (initial_dist times origins destinations latest counts : list Z)
    (alpha beta delta : list Z) (gamma lower_total : Z) : Prop :=
  ChainDualCertificate
    n budget initial_dist latest counts alpha beta delta gamma
    (lower_total +
     sum (fun passenger => 0 <= passenger < m)
         (fun passenger => Znth passenger times 0)).
Definition SelectedDualCertificate
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) (best : Z) : Prop :=
  exists current_total alpha beta delta,
    PassengerTravelTotal m times destinations arrivals current_total /\
    SightseeingDualLowerBound
      n m (budget - remaining)
      initial_dist times origins destinations latest counts
      alpha beta delta best current_total.
Inductive GreedyShadowTrace
    (n m budget : Z)
    (initial_dist times origins destinations latest counts : list Z)
    : Z -> list Z -> list Z -> Prop :=
| GreedyShadowTrace_base :
    forall initial_arrivals initial_total,
      BusArrivalSchedule n initial_dist latest initial_arrivals ->
      PassengerTravelTotal
        m times destinations initial_arrivals initial_total ->
      GreedyShadowTrace
        n m budget initial_dist times origins destinations latest counts
        0 initial_dist initial_arrivals
| GreedyShadowTrace_step :
    forall spent old_dist old_arrivals new_dist new_arrivals
           old_total best position alpha beta delta,
      GreedyShadowTrace
        n m budget initial_dist times origins destinations latest counts
        spent old_dist old_arrivals ->
      0 < best ->
      BestBoostChoice
        n old_dist counts latest old_arrivals best position ->
      PassengerTravelTotal
        m times destinations old_arrivals old_total ->
      SightseeingDualLowerBound
        n m spent initial_dist times origins destinations latest counts
        alpha beta delta best old_total ->
      ArrivalRepairOutcome
        n old_dist old_arrivals new_dist new_arrivals latest position ->
      GreedyShadowTrace
        n m budget initial_dist times origins destinations latest counts
        (spent + 1) new_dist new_arrivals.
Definition TracedBoosterProgress
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  BoosterProgress
    n m budget remaining initial_dist times origins destinations
    dist latest counts arrivals /\
  GreedyShadowTrace
    n m budget initial_dist times origins destinations latest counts
    (budget - remaining) dist arrivals.

(* ------------------------------------------------------------------------- *)
(* Direct combinatorial adjacent-budget exchange certificate. *)
Definition SelectedExchangeCertificate
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) (best : Z) : Prop :=
  0 <= best /\
  exists current_total,
    PassengerTravelTotal m times destinations arrivals current_total /\
    forall candidate_total,
      SightseeingCandidateTotal
        n m (budget - remaining + 1)
        initial_dist times origins destinations candidate_total ->
      current_total - best <= candidate_total.
