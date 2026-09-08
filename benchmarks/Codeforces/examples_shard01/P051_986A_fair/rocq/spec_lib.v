(* Codeforces 986/A - Fair: for every town, the least total road cost of bringing
   in s different types of goods from the nearest towns producing them. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Require Import GraphLib.reachable.reachable_basic.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphDistanceZ.

Import ListNotations.
Local Open Scope Z_scope.

(* The towns as a graph value: the towns 1 .. n and the roads between them. *)
Definition TownGraph (n : Z) (e : list (Z * Z)%type) : ZGraph :=
  {| zv := fun x => 1 <= x <= n ; ze := fun x y => In (x, y) e \/ In (y, x) e |}.

(* How many roads the shortest route between two towns uses.
   [zdistance] is the repository's Z-indexed graph distance: the least length
   of a walk from u to v, taken with MaxMinLib's minimum. *)
Definition Distance (n : Z) (e : list (Z * Z)%type) (u v d : Z) : Prop :=
  1 <= u <= n /\ 1 <= v <= n /\ zdistance (TownGraph n e) u v d.

(* How far the nearest town producing that type of goods lies. *)
Definition TypeDistance (n : Z) (e : list (Z * Z)%type) (goods : list Z) (town typ d : Z) : Prop :=
  min_value_of_subset Z.le
    (fun q => exists src, 1 <= src <= n /\ Znth (src - 1) goods 0 = typ /\
                Distance n e town src q)
    (fun x => x) d.

(* The s different types of goods a fair brings in. *)
Definition TypeChoice (s : Z) (types : list Z) : Prop :=
  Zlength types = s /\ NoDup types /\ Forall (fun x => 1 <= x) types.

(* What holding the fair in that town costs: the distances to the chosen types,
   added up. *)
Definition FairCost (n s : Z) (e : list (Z * Z)%type) (goods : list Z) (town cost : Z) : Prop :=
  exists types ds : list Z,
    TypeChoice s types /\ Zlength ds = s /\
    (forall i, 0 <= i < s -> TypeDistance n e goods town (Znth i types 0) (Znth i ds 0)) /\
    cost = fold_right Z.add 0 ds.
Definition Pre (k s : Z) (e : list (Z * Z)%type) (goods : list Z) : Prop :=
  (* Stated explicitly in the P051 solver Require, so dropped here:
       1 <= Zlength goods <= 100000 /\
       1 <= s <= k /\
       k <= Zlength goods /\
       Forall (fun x => 1 <= x <= k) goods /\
       Forall (fun p => 1 <= fst p <= (Zlength goods) /\ 1 <= snd p <= (Zlength goods) /\ fst p <> snd p) e  *)
  (forall typ, 1 <= typ <= k -> In typ goods) /\
  connected (TownGraph (Zlength goods) e) /\
  forall p q, In p e -> In q e -> (p = q \/ p = (snd q, fst q)) -> p = q.

(* One answer per town: |out| = |goods| and
     out[i] = min { cost : FairCost for town i + 1 }
   the cheapest choice of s distinct goods types for a fair held in that town. *)
Definition Spec (k s : Z) (e : list (Z * Z)%type) (goods out : list Z) : Prop :=
  Zlength out = Zlength goods /\ forall i, 0 <= i < Zlength goods ->
  min_value_of_subset Z.le (FairCost (Zlength goods) s e goods (i + 1))
    (fun x => x) (Znth i out 0).
