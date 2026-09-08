Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P053_1594D_the_number_of_imposters.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition comment_at (comments : list (Z * Z * Z)) (i : Z) : Z * Z * Z :=
  Znth i comments (0, 0, 0).

Definition edge_src (comments : list (Z * Z * Z)) (e : Z) : Z :=
  let '(u, v, _) := comment_at comments (e / 2) in
  if Z.even e then u else v.

Definition edge_dst (comments : list (Z * Z * Z)) (e : Z) : Z :=
  let '(u, v, _) := comment_at comments (e / 2) in
  if Z.even e then v else u.

Definition edge_wt (comments : list (Z * Z * Z)) (e : Z) : Z :=
  let '(_, _, w) := comment_at comments (e / 2) in w.

(* Following [nxt] from an edge index until [-1] yields this list. *)

Inductive AdjChain (ns : list Z) : Z -> list Z -> Prop :=
  | adj_end  : AdjChain ns (-1) nil
  | adj_cons : forall e rest,
      0 <= e -> AdjChain ns (Znth e ns 0) rest -> AdjChain ns e (e :: rest).

(* The arrays encode the first [k] comments as a forward star. *)

Definition ForwardStar (n cap k : Z) (hs ns ts ws : list Z)
    (comments : list (Z * Z * Z)) : Prop :=
  Zlength hs = n + 1 /\
  Zlength ns = 2 * cap /\ Zlength ts = 2 * cap /\ Zlength ws = 2 * cap /\
  0 <= k <= cap /\ k <= Zlength comments /\
  (forall e, 0 <= e < 2 * k ->
     Znth e ts 0 = edge_dst comments e /\ Znth e ws 0 = edge_wt comments e) /\
  (forall u, 1 <= u <= n ->
     exists es, AdjChain ns (Znth u hs 0) es /\ NoDup es /\
       forall e, In e es <-> (0 <= e < 2 * k /\ edge_src comments e = u)).

Definition ColourValues (n : Z) (cs : list Z) : Prop :=
  Zlength cs = n + 1 /\
  forall v, 1 <= v <= n ->
    Znth v cs 0 = -1 \/ Znth v cs 0 = 0 \/ Znth v cs 0 = 1.

Definition ParityRespected (comments : list (Z * Z * Z)) (cs : list Z) : Prop :=
  forall i, 0 <= i < Zlength comments ->
    let '(u, v, w) := comment_at comments i in
    Znth u cs 0 <> -1 -> Znth v cs 0 <> -1 ->
    Znth v cs 0 = Z.lxor (Znth u cs 0) w.

Definition ColouredClosed (comments : list (Z * Z * Z)) (cs : list Z) : Prop :=
  forall i, 0 <= i < Zlength comments ->
    let '(u, v, _) := comment_at comments i in
    (Znth u cs 0 <> -1 <-> Znth v cs 0 <> -1).

Definition OnSet (n : Z) (cs r : list Z) : Prop :=
  Zlength r = n /\
  (forall v, 1 <= v <= n -> Znth v cs 0 <> -1 ->
     Znth (v - 1) r 0 = 0 \/ Znth (v - 1) r 0 = 1) /\
  (forall v, 1 <= v <= n -> Znth v cs 0 = -1 -> Znth (v - 1) r 0 = 0).

Definition ConsistentOn (n : Z) (comments : list (Z * Z * Z))
    (cs r : list Z) : Prop :=
  OnSet n cs r /\
  forall i, 0 <= i < Zlength comments ->
    let '(u, v, w) := comment_at comments i in
    Znth u cs 0 <> -1 -> Znth v cs 0 <> -1 ->
    Znth (v - 1) r 0 = Z.lxor (Znth (u - 1) r 0) w.

Definition MaxImpostersOn (n : Z) (comments : list (Z * Z * Z))
    (cs : list Z) (t : Z) : Prop :=
  max_value_of_subset Z.le
    (fun x => exists r, ConsistentOn n comments cs r /\
                         x = fold_right Z.add 0 r)
    (fun x => x) t.

(* Initialization prefixes.  These are pure facts about whole-array ghost
   lists, so untouched cells (especially index 0) remain owned by [full]. *)

Definition HeadsInitialised (hs : list Z) (next : Z) : Prop :=
  forall v, 1 <= v < next -> Znth v hs 0 = -1.

Definition ColoursInitialised (cs : list Z) (next : Z) : Prop :=
  forall v, 1 <= v < next -> Znth v cs 0 = -1.

(* Machine-level range facts kept separate from the mathematical encoding. *)

Definition ForwardStarRanges (n k : Z) (hs ns ts ws : list Z) : Prop :=
  (forall u, 1 <= u <= n -> -1 <= Znth u hs 0 < 2 * k) /\
  (forall e, 0 <= e < 2 * k ->
     -1 <= Znth e ns 0 < 2 * k /\
     1 <= Znth e ts 0 <= n /\
     (Znth e ws 0 = 0 \/ Znth e ws 0 = 1)).

(* [vs] is exactly the set newly coloured since [before]. *)

Definition NewColourSet (n : Z) (before after vs : list Z) : Prop :=
  NoDup vs /\ Forall (fun v => 1 <= v <= n) vs /\
  (forall v, 1 <= v <= n ->
     (In v vs <-> Znth v before 0 = -1 /\ Znth v after 0 <> -1)) /\
  (forall v, 1 <= v <= n -> ~ In v vs ->
     Znth v after 0 = Znth v before 0).

Definition ColourCount (cs vertices : list Z) (bit count : Z) : Prop :=
  count = Z.of_nat
    (count_occ Z.eq_dec (map (fun v => Znth v cs 0) vertices) bit).

(* This is the propagation conclusion needed from connectivity, stated
   directly in the frontier instead of introducing a graph/reachability
   object.  Every consistent assignment differs from the current component
   colouring by one common bit. *)

Definition ComponentTwoChoices (n : Z) (comments : list (Z * Z * Z))
    (cs vertices : list Z) : Prop :=
  forall roles, RolesConsistent n comments roles ->
    exists flip, (flip = 0 \/ flip = 1) /\
      forall v, In v vertices ->
        Znth (v - 1) roles 0 = Z.lxor (Znth v cs 0) flip.

(* Every outgoing edge of a finished vertex has been traversed without a
   conflict; traversal also guarantees that the neighbour is coloured. *)

Definition FullyScanned (comments : list (Z * Z * Z))
    (cs finished : list Z) : Prop :=
  forall e, 0 <= e < 2 * Zlength comments -> In (edge_src comments e) finished ->
    Znth (edge_dst comments e) cs 0 <> -1 /\
    Znth (edge_dst comments e) cs 0 =
      Z.lxor (Znth (edge_src comments e) cs 0) (edge_wt comments e).

(* While scanning one vertex, [cur] names the remaining suffix of its
   forward-star chain; all edges outside that suffix are already respected. *)

Definition ScanAt (comments : list (Z * Z * Z)) (ns cs : list Z)
    (u cur : Z) : Prop :=
  exists remaining,
    AdjChain ns cur remaining /\
    (forall e, 0 <= e < 2 * Zlength comments ->
       edge_src comments e = u -> ~ In e remaining ->
       Znth (edge_dst comments e) cs 0 <> -1 /\
       Znth (edge_dst comments e) cs 0 =
         Z.lxor (Znth u cs 0) (edge_wt comments e)).

(* Stack-loop head: [finished] has been popped and fully scanned; [pending]
   is exactly the live stack prefix.  Counts cover [finished] only. *)

Definition ComponentFrontier (n : Z) (comments : list (Z * Z * Z))
    (before after finished pending : list Z) (c0 c1 : Z) : Prop :=
  ColourValues n after /\
  NewColourSet n before after (finished ++ pending) /\
  ComponentTwoChoices n comments after (finished ++ pending) /\
  FullyScanned comments after finished /\
  ColourCount after finished 0 c0 /\ ColourCount after finished 1 c1.

(* Inner adjacency-loop head.  The current [u] has already been counted but
   is not fully scanned until [cur] reaches [-1]. *)

Definition ComponentScan (n : Z) (comments : list (Z * Z * Z))
    (ns before after finished pending : list Z) (u cur c0 c1 : Z) : Prop :=
  ColourValues n after /\
  NewColourSet n before after (finished ++ u :: pending) /\
  ComponentTwoChoices n comments after (finished ++ u :: pending) /\
  FullyScanned comments after finished /\
  ScanAt comments ns after u cur /\
  ColourCount after (finished ++ u :: nil) 0 c0 /\
  ColourCount after (finished ++ u :: nil) 1 c1.

(* Normal stack-loop exit.  Besides the concrete frontier facts, this is the
   constructive B4 bridge used by the outer loop. *)

Definition ComponentComplete (n : Z) (comments : list (Z * Z * Z))
    (before after vertices : list Z) (c0 c1 : Z) : Prop :=
  ComponentFrontier n comments before after vertices nil c0 c1 /\
  ParityRespected comments after /\ ColouredClosed comments after /\
  (forall t, MaxImpostersOn n comments before t ->
     MaxImpostersOn n comments after (t + Z.max c0 c1)).

(* ================================================================= *)
(*  Strengthened retry interface.  The declarations above are retained *)
(*  unchanged; these additional Props close two structural gaps found  *)
(*  by the first VC-checking pass.                                     *)
(* ================================================================= *)

(* A role list that is consistent on one explicitly named vertex set.
   It is independent of contradictions in every other uncoloured
   component, unlike a global [RolesConsistent] premise. *)

Definition RolesConsistentOnVertices (n : Z)
    (comments : list (Z * Z * Z)) (vertices roles : list Z) : Prop :=
  Zlength roles = n /\
  (forall v, In v vertices ->
     Znth (v - 1) roles 0 = 0 \/ Znth (v - 1) roles 0 = 1) /\
  (forall i, 0 <= i < Zlength comments ->
     let '(u, v, w) := comment_at comments i in
     In u vertices -> In v vertices ->
     Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w).

(* B2 in component-local form: every locally consistent role assignment
   differs from the solver's colouring by one common bit. *)

Definition ComponentTwoChoicesLocal (n : Z)
    (comments : list (Z * Z * Z)) (cs vertices : list Z) : Prop :=
  forall roles, RolesConsistentOnVertices n comments vertices roles ->
    exists flip, (flip = 0 \/ flip = 1) /\
      forall v, In v vertices ->
        Znth (v - 1) roles 0 = Z.lxor (Znth v cs 0) flip.

(* The live chain really is the unscanned suffix for [u]: every edge still
   reachable from [cur] belongs to [u]'s forward-star adjacency list. *)

Definition ScanAtOwned (comments : list (Z * Z * Z)) (ns cs : list Z)
    (u cur : Z) : Prop :=
  ScanAt comments ns cs u cur /\
  exists remaining,
    AdjChain ns cur remaining /\
    forall e, In e remaining -> edge_src comments e = u.

Definition ComponentFrontierStrong (n : Z)
    (comments : list (Z * Z * Z))
    (before after finished pending : list Z) (c0 c1 : Z) : Prop :=
  ComponentFrontier n comments before after finished pending c0 c1 /\
  ComponentTwoChoicesLocal n comments after (finished ++ pending).

Definition ComponentScanStrong (n : Z)
    (comments : list (Z * Z * Z))
    (ns before after finished pending : list Z) (u cur c0 c1 : Z) : Prop :=
  ComponentScan n comments ns before after finished pending u cur c0 c1 /\
  ScanAtOwned comments ns after u cur /\
  ComponentTwoChoicesLocal n comments after (finished ++ u :: pending).

Definition ComponentCompleteStrong (n : Z)
    (comments : list (Z * Z * Z))
    (before after vertices : list Z) (c0 c1 : Z) : Prop :=
  ComponentComplete n comments before after vertices c0 c1 /\
  ComponentTwoChoicesLocal n comments after vertices.
