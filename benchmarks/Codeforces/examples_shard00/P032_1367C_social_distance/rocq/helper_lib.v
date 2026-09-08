Require Import PVbench.Codeforces.examples_shard00.P032_1367C_social_distance.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(** [RightNearest] gives the first originally occupied table at or to the
    right of [from].  [Zlength s + k] is the sentinel used when that suffix
    contains no occupied table. *)
Definition RightNearest
    (s : list Z) (k from nearest : Z) : Prop :=
  0 <= from <= Zlength s /\
  ((nearest = Zlength s + k /\
    forall j, from <= j < Zlength s -> Znth j s 48 <> 49) \/
   (from <= nearest < Zlength s /\
    Znth nearest s 48 = 49 /\
    forall j, from <= j < nearest -> Znth j s 48 <> 49)).

(** Pointwise meaning of the initialized suffix of the auxiliary table. *)
Definition RightNearestSuffix
    (s : list Z) (k from : Z) (values : list Z) : Prop :=
  Zlength values = Zlength s - from /\
  forall off, 0 <= off < Zlength values ->
    RightNearest s k (from + off) (Znth off values 0).

(** [LastOccupiedBefore] gives the rightmost original or additional occupied
    position in the processed prefix.  The negative value [-k-1] is the same
    canonical sentinel used by the C loop when that prefix is empty. *)
Definition LastOccupiedBefore
    (s : list Z) (k : Z) (extra : Z -> Prop)
    (processed last : Z) : Prop :=
  (last = - k - 1 /\
   forall j, 0 <= j < processed ->
     ~ ((0 <= j < Zlength s /\ Znth j s 48 = 49) \/ extra j)) \/
  (0 <= last < processed /\
   ((0 <= last < Zlength s /\ Znth last s 48 = 49) \/ extra last) /\
   forall j, last < j < processed ->
     ~ ((0 <= j < Zlength s /\ Znth j s 48 = 49) \/ extra j)).

(** Mathematical state of a left-to-right greedy placement.  It exposes an
    actually chosen feasible set, the last occupied position, its cardinality,
    and optimality among all feasible additions restricted to the processed
    prefix.  Among equally large prefix placements, the chosen placement ends
    no later than a competitor.  This canonical dominance is what makes a
    left-distance skip preserve optimality.  The predicate is independent of
    how the program finds that set. *)
Definition PrefixPlacementState
    (s : list Z) (k processed last answer : Z) : Prop :=
  0 <= processed <= Zlength s /\
  exists extra : Z -> Prop,
    AdditionalTables s k extra /\
    (forall j, extra j -> j < processed) /\
    answer = #(fun j : Z => 0 <= j < processed /\ extra j) /\
    LastOccupiedBefore s k extra processed last /\
    (forall competitor : Z -> Prop,
      AdditionalTables s k competitor ->
      #(fun j : Z => 0 <= j < processed /\ competitor j) <= answer) /\
    forall competitor,
      AdditionalTables s k competitor ->
      #(fun j : Z => 0 <= j < processed /\ competitor j) = answer ->
      exists competitor_last,
        LastOccupiedBefore s k competitor processed competitor_last /\
        last <= competitor_last.
