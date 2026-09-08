Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Require Import GraphLib.reachable.reachable_basic.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphDistanceZ.
Require Import PVbench.Codeforces.examples_shard01.P051_986A_fair.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition SrcSet (n : Z) (goods : list Z) (c u : Z) : Prop :=
  1 <= u <= n /\ Znth (u - 1) goods 0 = c.

(* A walk of [d] roads reaching [v] from some town producing type [c]. *)

Definition MReach (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                  (c v d : Z) : Prop :=
  exists u, SrcSet n goods c u /\ path_of_zlen (TownGraph n e) u v d.

(* The shortest such walk: what one BFS run stores in [dist_[c][v]].
   This is the plain two-part form of [TypeDistance]. *)

Definition BfsDist (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                   (c v d : Z) : Prop :=
  MReach n e goods c v d /\ forall q, MReach n e goods c v q -> d <= q.

(* ---- adjacency arcs -------------------------------------------- *)

(* Road [i] contributes arc [2*i] (from [eu[i]] to [ev[i]]) and arc
   [2*i+1] (the reverse). *)

Definition ArcFrom (edges : list (Z * Z)%type) (j : Z) : Z :=
  if Z.even j then fst (Znth (j / 2) edges (0, 0))
              else snd (Znth (j / 2) edges (0, 0)).

Definition ArcTo (edges : list (Z * Z)%type) (j : Z) : Z :=
  if Z.even j then snd (Znth (j / 2) edges (0, 0))
              else fst (Znth (j / 2) edges (0, 0)).

(* [AdjChain nx cur l]: following [nxt_] from [cur] visits exactly [l].
   The recursion is on the derivation, so no decreasing measure on the
   index is needed. *)

Inductive AdjChain (nx : list Z) : Z -> list Z -> Prop :=
| AdjChain_nil : AdjChain nx (-1) nil
| AdjChain_cons : forall j l,
    0 <= j < Zlength nx ->
    AdjChain nx (Znth j nx 0) l ->
    AdjChain nx j (j :: l).

(* The chain hanging off [head_[u]] is exactly the set of arcs leaving [u]. *)

Definition AdjListAt (done : Z) (edges : list (Z * Z)%type)
                     (hd nx : list Z) (u : Z) (l : list Z) : Prop :=
  AdjChain nx (Znth (u - 1) hd 0) l /\ NoDup l /\
  (forall j, In j l -> 0 <= j < 2 * done /\ ArcFrom edges j = u) /\
  (forall j, 0 <= j < 2 * done -> ArcFrom edges j = u -> In j l).

(* After [done] roads have been inserted, the three work arrays are a
   faithful adjacency-list representation of those roads. *)

Definition AdjBuild (n done : Z) (edges : list (Z * Z)%type)
                    (hd nx tlst : list Z) : Prop :=
  Zlength hd = n /\ Zlength nx = 2 * done /\ Zlength tlst = 2 * done /\
  (forall j, 0 <= j < 2 * done -> Znth j tlst 0 = ArcTo edges j) /\
  (forall j, 0 <= j < 2 * done ->
     Znth j nx 0 = -1 \/ 0 <= Znth j nx 0 < 2 * done) /\
  (forall u, 1 <= u <= n ->
     Znth (u - 1) hd 0 = -1 \/ 0 <= Znth (u - 1) hd 0 < 2 * done) /\
  (forall u, 1 <= u <= n -> exists l, AdjListAt done edges hd nx u l).

(* ---- the BFS loop state ---------------------------------------- *)

(* What the queue and the distance row mean, independently of how far
   the expansion has progressed.  [dl] is the whole [dist_] row, read at
   the town index; [Q] is the live part of [queue_]. *)

Definition BfsCore (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                   (c : Z) (Q dl : list Z) : Prop :=
  (forall i, 0 <= i < Zlength Q -> 1 <= Znth i Q 0 <= n) /\
  NoDup Q /\
  (forall v, 1 <= v <= n -> (In v Q <-> 0 <= Znth v dl 0)) /\
  (forall v, 1 <= v <= n -> ~ In v Q -> Znth v dl 0 = -1) /\
  (forall i, 0 <= i < Zlength Q ->
     MReach n e goods c (Znth i Q 0) (Znth (Znth i Q 0) dl 0)) /\
  (forall i j, 0 <= i -> i <= j -> j < Zlength Q ->
     Znth (Znth i Q 0) dl 0 <= Znth (Znth j Q 0) dl 0) /\
  (forall i, 0 <= i < Zlength Q -> 0 <= Znth (Znth i Q 0) dl 0 <= i) /\
  (forall v, 1 <= v <= n -> Znth (v - 1) goods 0 = c ->
     In v Q /\ Znth v dl 0 = 0).

(* The first [qh] queue entries have had all their roads relaxed. *)

Definition BfsExpanded (n : Z) (e : list (Z * Z)%type)
                       (Q dl : list Z) (qh : Z) : Prop :=
  forall i w, 0 <= i < qh -> 1 <= w <= n ->
    (In (Znth i Q 0, w) e \/ In (w, Znth i Q 0) e) ->
    In w Q /\ Znth w dl 0 <= Znth (Znth i Q 0) dl 0 + 1.

(* Nothing in the queue is further out than [b]: the two-level property. *)

Definition BfsBounded (Q dl : list Z) (b : Z) : Prop :=
  forall j, 0 <= j < Zlength Q -> Znth (Znth j Q 0) dl 0 <= b.

(* The inner arc scan: every arc of [u] outside the remaining chain has
   already been relaxed. *)

Definition BfsScan (done : Z) (edges : list (Z * Z)%type)
                   (nx tlst Q dl : list Z) (u cur : Z) : Prop :=
  exists lrem,
    AdjChain nx cur lrem /\
    (forall j, In j lrem -> 0 <= j < 2 * done /\ ArcFrom edges j = u) /\
    (forall j, 0 <= j < 2 * done -> ArcFrom edges j = u -> ~ In j lrem ->
       In (Znth j tlst 0) Q /\
       Znth (Znth j tlst 0) dl 0 <= Znth u dl 0 + 1).

(* ---- the solver's own loop states ------------------------------ *)

(* The first [done - 1] rows of [dist_] hold real multi-source distances. *)

Definition BfsRows (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                   (rows : list (list Z)) (done : Z) : Prop :=
  forall c v, 1 <= c < done -> 1 <= v <= n ->
    0 <= Znth v (Znth c rows nil) 0 <= n - 1 /\
    BfsDist n e goods c v (Znth v (Znth c rows nil) 0).

(* [tmp_[0 .. done)] holds town [v]'s distances to types [1 .. done]. *)

Definition TmpPrefix (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                     (v : Z) (tmpl : list Z) (done : Z) : Prop :=
  forall j, 0 <= j < done ->
    0 <= Znth j tmpl 0 <= n - 1 /\
    BfsDist n e goods (j + 1) v (Znth j tmpl 0).

(* [cost[1 .. done]] already holds optimal fair costs. *)

Definition OutPrefix (n s : Z) (e : list (Z * Z)%type) (goods : list Z)
                     (out : list Z) (done : Z) : Prop :=
  forall i, 0 <= i < done ->
    min_value_of_subset Z.le (FairCost n s e goods (i + 1)) (fun x => x)
      (Znth i out 0).

(* The machine-level ranges the arc arrays satisfy; kept apart from
   [AdjBuild] because the C loop needs them at every array access. *)

Definition NxtRange (done : Z) (nx : list Z) : Prop :=
  forall j, 0 <= j < 2 * done -> -1 <= Znth j nx 0 < 2 * done.

Definition ArcToRange (n done : Z) (tlst : list Z) : Prop :=
  forall j, 0 <= j < 2 * done -> 1 <= Znth j tlst 0 <= n.

(* What one [bfs_type] run leaves in its row: every town is either
   unreachable from the type-[c] towns, or holds the true distance. *)

Definition BfsRowResult (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                        (c : Z) (dl : list Z) : Prop :=
  forall v, 1 <= v <= n ->
    (Znth v dl 0 = -1 /\ ~ (exists q, MReach n e goods c v q)) \/
    (0 <= Znth v dl 0 <= n - 1 /\ BfsDist n e goods c v (Znth v dl 0)).

(* The source-collecting loop: towns below [done] are already classified,
   towns from [done] on still hold the initial [-1]. *)

Definition BfsInit (n : Z) (goods : list Z) (c : Z)
                   (Q dl : list Z) (done : Z) : Prop :=
  NoDup Q /\
  (forall w, 1 <= w < done -> Znth (w - 1) goods 0 = c ->
     In w Q /\ Znth w dl 0 = 0) /\
  (forall w, 1 <= w < done -> Znth (w - 1) goods 0 <> c -> Znth w dl 0 = -1) /\
  (forall w, done <= w <= n -> Znth w dl 0 = -1) /\
  (forall i, 0 <= i < Zlength Q ->
     1 <= Znth i Q 0 < done /\
     Znth (Znth i Q 0 - 1) goods 0 = c /\
     Znth (Znth i Q 0) dl 0 = 0).

(* [FairCost] adds the chosen distances with [fold_right Z.add 0]; the C
   accumulator does the same, under a name that does not clash with the
   local variable [sum]. *)

Definition ZSum (l : list Z) : Z := fold_right Z.add 0 l.

(* ================================================================= *)
(*  Bridge 0.  Roads have no direction, so distance is symmetric.     *)
(* ================================================================= *)
