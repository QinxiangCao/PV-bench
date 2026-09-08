Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import GraphLib.graph_basic.

Require Import GraphLib.reachable.vpath.

Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.

Import ListNotations.

Local Open Scope Z_scope.

Definition Degree (e : list (Z * Z)) (v : Z) : Z :=
  Zlength (filter (fun p => orb (Z.eqb (fst p) v) (Z.eqb (snd p) v)) e).

Definition HedgehogGraph (e : list (Z * Z)) : ZGraph :=
  {| zv := fun _ => True;
     ze := fun x y => In (x,y) e \/ In (y,x) e |}.

Definition HedgehogPath (e : list (Z * Z)) (u v : Z) (path : list Z) : Prop :=
  valid_vpath (HedgehogGraph e) u path v /\ NoDup path.

Definition CanonicalEdge (edge : Z * Z) : Z * Z :=
  if Z.leb (fst edge) (snd edge) then edge else (snd edge, fst edge).

Definition CurrentEdgeFresh (edges : list (Z * Z)) (index : Z) : Prop :=
  0 <= index < Zlength edges ->
  let edge := Znth index edges (0, 0) in
  fst edge <> snd edge /\
  ~ In (CanonicalEdge edge)
      (map CanonicalEdge (sublist 0 index edges)).

Definition TreeInput (n : Z) (e : list (Z * Z)) : Prop :=
  1 <= n <= 100000 /\ Zlength e = n - 1 /\
  Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
  (forall index, CurrentEdgeFresh e index) /\
  forall v, 1 <= v <= n -> exists path, HedgehogPath e 1 v path.

Definition DegreePrefix
    (n : Z) (edges : list (Z * Z)) (done : Z)
    (degrees : list Z) : Prop :=
  Zlength degrees = n /\
  forall v, 0 <= v < n ->
    Znth v degrees 0 = Degree (sublist 0 done edges) (v + 1).

Definition GraphDistance
    (edges : list (Z * Z)) (source vertex distance : Z) : Prop :=
  exists path,
    HedgehogPath edges source vertex path /\
    distance = Zlength path - 1 /\
    forall other,
      HedgehogPath edges source vertex other ->
      Zlength path <= Zlength other.

Definition HedgehogVertexOK
    (k center vertex distance degree : Z) : Prop :=
  distance <= k /\
  (distance = k -> degree = 1) /\
  (distance < k ->
    (vertex = center -> 3 <= degree) /\
    (vertex <> center -> 4 <= degree)).

Definition HedgehogLayers (n k center : Z) (e : list (Z * Z)) : Prop :=
  1 <= center <= n /\
  forall vertex, 1 <= vertex <= n ->
    exists distance,
      GraphDistance e center vertex distance /\
      HedgehogVertexOK k (center - 1) (vertex - 1)
        distance (Degree e vertex).

Definition Spec (n k : Z) (e : list (Z * Z)) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists center, HedgehogLayers n k center e).

Definition BFSParentState
    (n : Z) (edges : list (Z * Z)) (source : Z)
    (parents distances : list Z) : Prop :=
  Znth source parents (-1) = -1 /\
  forall v, 0 <= v < n -> v <> source ->
    0 <= Znth v distances (-1) ->
    0 <= Znth v parents (-1) < n /\
    (In (v + 1, Znth v parents (-1) + 1) edges \/
     In (Znth v parents (-1) + 1, v + 1) edges) /\
    Znth v distances (-1) = Znth (Znth v parents (-1)) distances (-1) + 1.

Definition BFSData
    (n : Z) (edges : list (Z * Z)) (source : Z)
    (parents distances : list Z) : Prop :=
  Zlength parents = n /\
  Zlength distances = n /\
  0 <= source < n /\
  BFSParentState n edges source parents distances /\
  (forall v, 0 <= v < n ->
    GraphDistance edges (source + 1) (v + 1) (Znth v distances (-1))).

Definition BFSResult
    (n : Z) (edges : list (Z * Z)) (source : Z)
    (parents distances : list Z) (farthest : Z) : Prop :=
  BFSData n edges source parents distances /\
  0 <= farthest < n /\
  forall v, 0 <= v < n ->
    Znth v distances (-1) <= Znth farthest distances (-1).

Definition BFSQueueState
    (n : Z) (edges : list (Z * Z)) (source processed farthest : Z)
    (queue parents distances : list Z) : Prop :=
  Zlength parents = n /\
  Zlength distances = n /\
  0 <= processed <= Zlength queue /\
  1 <= Zlength queue <= n /\
  NoDup queue /\
  Znth 0 queue 0 = source /\
  0 <= source < n /\
  0 <= farthest < n /\
  BFSParentState n edges source parents distances /\
  (forall q, 0 <= q < Zlength queue ->
    0 <= Znth q queue 0 < n /\
    0 <= Znth (Znth q queue 0) distances (-1)) /\
  (forall v, 0 <= v < n ->
    (In v queue <-> 0 <= Znth v distances (-1))) /\
  (forall q, 0 <= q < processed ->
    Znth (Znth q queue 0) distances (-1) <=
    Znth farthest distances (-1)) /\
  (forall q neighbor, 0 <= q < processed ->
    (In (Znth q queue 0 + 1, neighbor + 1) edges \/
     In (neighbor + 1, Znth q queue 0 + 1) edges) ->
    In neighbor queue) /\
  forall v, 0 <= v < n ->
    0 <= Znth v distances (-1) ->
    GraphDistance edges (source + 1) (v + 1) (Znth v distances (-1)).

Definition BFSFrontierState
    (n : Z) (edges : list (Z * Z)) (source vertex : Z)
    (distances : list Z) : Prop :=
  forall neighbor,
    0 <= neighbor < n ->
    (In (vertex + 1, neighbor + 1) edges \/
     In (neighbor + 1, vertex + 1) edges) ->
    Znth neighbor distances (-1) < 0 ->
    GraphDistance edges (source + 1) (neighbor + 1)
      (Znth vertex distances (-1) + 1).

Definition BFSFrontierComplete (n : Z) (edges : list (Z * Z)) : Prop :=
  forall source processed farthest queue parents distances,
    BFSQueueState n edges source processed farthest queue parents distances ->
    processed < Zlength queue ->
    BFSFrontierState n edges source (Znth processed queue 0) distances.

Definition AncestorAfter
    (parents : list Z) (start steps vertex : Z) : Prop :=
  exists path,
    Zlength path = steps + 1 /\
    Znth 0 path 0 = start /\
    Znth steps path 0 = vertex /\
    forall i, 0 <= i < steps ->
      Znth (i + 1) path 0 = Znth (Znth i path 0) parents (-1).

Definition DecisionPrefix
    (n k center done ok : Z) (degrees distances : list Z) : Prop :=
  (ok = 0 \/ ok = 1) /\
  (ok = 1 <->
    forall v, 0 <= v < done ->
      HedgehogVertexOK k center v
        (Znth v distances (-1)) (Znth v degrees 0)).

Definition SolverDecision
    (n k : Z) (edges : list (Z * Z))
    (second_parent second_dist : list Z) (endpoint center : Z)
    (center_parent center_dist degrees : list Z) (done out : Z) : Prop :=
  (out = 0 /\ Znth endpoint second_dist 0 <> 2 * k) \/
  (Znth endpoint second_dist 0 = 2 * k /\
   AncestorAfter second_parent endpoint k center /\
   BFSData n edges center center_parent center_dist /\
   DecisionPrefix n k center done out degrees center_dist).

Definition HedgehogDecisionComplete
    (n k : Z) (edges : list (Z * Z)) : Prop :=
  forall first_parent first_dist first_endpoint
         second_parent second_dist second_endpoint center
         center_parent center_dist degrees,
    BFSResult n edges 0 first_parent first_dist first_endpoint ->
    BFSResult n edges first_endpoint second_parent second_dist second_endpoint ->
    DegreePrefix n edges (n - 1) degrees ->
    SolverDecision n k edges second_parent second_dist second_endpoint center
      center_parent center_dist degrees n 0 ->
    ~ exists candidate, HedgehogLayers n k candidate edges.

Definition GraphPre (n : Z) (e : list (Z * Z)) : Prop :=
  TreeInput n e /\
  BFSFrontierComplete n e /\
  forall k, 1 <= k <= 1000000000 -> HedgehogDecisionComplete n k e.

Definition Pre (n k : Z) (e : list (Z * Z)) : Prop :=
  1 <= k <= 1000000000 /\ GraphPre n e.
