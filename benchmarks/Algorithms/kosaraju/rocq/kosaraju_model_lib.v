Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
(* From MonadLib.MonadErr Require Import StateRelBasic StateRelHoare FixpointLib. *)
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrLoop MonadErrHoarePartial MonadErrLoop.
From GraphLib Require Import graph_basic reachable_basic.
Require Import PVbench.Algorithms.kosaraju.rocq.scc_lib.
Module SCC := PVbench.Algorithms.kosaraju.rocq.scc_lib.
Require Import BourbakiWitt.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Class KosarajuGraph (G V E : Type) := {
  kos_graph :: Graph G V E;
  kos_gvalid :: GValid G;
  kos_stepvalid :: StepValid G V E;
  kos_unique :: StepUniqueDirected G V E;
  kos_finite :: FiniteGraph G V E;
}.

Section Kosaraju.

Context {G V E: Type}
        `{KG: KosarajuGraph G V E}
        (g: G)
        (g_valid: gvalid g).

(* VListBijective (NoDup vertex list = exact |V|) derived from FiniteGraph. *)
#[local] Instance kos_vlist : VListBijective G V E :=
  finite_graph_vlist_bijective G V E.

(* ================================================================= *)
(* Program State — non-primitive inductive record (avoids Coq 8.20   *)
(* primitive record restrictions on intros/subst/destruct/rewrite)   *)
(* ================================================================= *)

Inductive St : Type := MkSt {
  timer    : nat;
  finish   : V -> nat;
  visited1 : V -> Prop;
  visited2 : V -> Prop;
  scc_id   : V -> nat;
  scc_next : nat;
}.

Definition init_st : St :=
  MkSt 0 (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0) 0.

(* ================================================================= *)
(* cardV: cardinality of a vertex predicate, counted over the NoDup   *)
(* vertex list bijective_listV g (= exact number of vertices |V|).    *)
(* Underpins the timer bound: timer <= cardV(visited1) <= |V|.         *)
(* ================================================================= *)

Fixpoint count_pred {A: Type} (P: A -> Prop) (l: list A) : nat :=
  match l with
  | nil => 0
  | x :: xs => match excluded_middle_informative (P x) with left _ => S (count_pred P xs) | right _ => count_pred P xs end
  end.

Definition cardV (P: V -> Prop) : nat := count_pred P (bijective_listV g).

Definition count_step {A: Type} (P: A -> Prop) (x: A) (n: nat) : nat :=
  match excluded_middle_informative (P x) with left _ => S n | right _ => n end.

(* If u does not occur in l, the predicates P and (P \/ =u) agree on l. *)

(* If u occurs (once, by NoDup) in l and ~ P u, adding "u=x" raises the count by 1. *)

(* visit1 u (u valid & not yet visited1) increases cardV(visited1) by exactly 1. *)

(* count_pred is monotone under pointwise implication (subset on the list's elements). *)

(* cardV is monotone: P ⊆ Q (pointwise on V) implies cardV P <= cardV Q. *)

(* visit1 u preserves the non-strict bound cardV(visited1) >= timer, with no
   precondition on whether u was already visited. Used to thread the assertS
   timer-bound through DFS_finish_f's loop without needing ~visited1/vvalid. *)

(* visit1 preserves the number of vertices with assigned finish times. *)

(* set_finish changes exactly one valid vertex from unfinished (0) to finished. *)

Definition FinishedCount (s : St) : Prop :=
  timer s = cardV (fun v => finish s v <> 0).

Definition UnvisitedFinishZero (s : St) : Prop :=
  forall v, ~ visited1 s v -> finish s v = 0.

Definition custom {Σ A: Type} (nrm: Σ -> A -> Σ -> Prop): MonadErr.M Σ A := {|
  MonadErr.nrm := nrm;
  MonadErr.err := ∅
|}.

Definition visit1 (u: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    visited1 st2 == visited1 st1 ∪ Sets.singleton u /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited2 st2 = visited2 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1).
    

Definition visit2 (u: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    visited2 st2 == visited2 st1 ∪ Sets.singleton u /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1).

Definition set_finish (u: V) (t: nat): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    timer st2 = S (timer st1) /\
    finish st2 u = S t /\
    (forall v, v <> u -> finish st2 v = finish st1 v) /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1).

Definition set_scc_id (u root: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    scc_id st2 u = scc_id st1 root /\
    (forall v, v <> u -> scc_id st2 v = scc_id st1 v) /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1 /\
    scc_next st2 = scc_next st1).

Definition set_scc_root_id (u: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    scc_id st2 u = scc_next st1 /\
    scc_next st2 = S (scc_next st1) /\
    (forall v, v <> u -> scc_id st2 v = scc_id st1 v) /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1).

(* ================================================================= *)
(* Inner DFS — Phase 1 (reversed graph)                              *)
(* ================================================================= *)

Definition step_rev (x y: V) : Prop := step g y x.
Definition reachable_rev (x y : V) : Prop := SCC.reachable_rev g x y.
Definition mutually_reachable (u v : V) : Prop := SCC.mutually_reachable g u v.

Definition TimerDominates (s: St) : Prop :=
  forall v, visited1 s v -> finish s v <= timer s.

Definition TimerDominates_except (s: St) (u: V) : Prop :=
  forall v, visited1 s v -> v <> u -> finish s v <= timer s.

Definition ReachRevClosed (s: St) : Prop :=
  forall v w, visited1 s v -> reachable_rev v w -> visited1 s w.

Definition DFSFinishInvCore (s : St) : Prop :=
  FinishedCount s /\
  UnvisitedFinishZero s /\
  cardV (visited1 s) >= timer s /\
  TimerDominates s.

Definition DFSFinishScoped (s : St) : Prop :=
  (forall v, ~ vvalid g v -> ~ visited1 s v) /\
  (forall v, ~ vvalid g v -> finish s v = 0).

Definition DFSFinishInv (s : St) : Prop :=
  DFSFinishInvCore s /\ DFSFinishScoped s.

Definition DFSFinishFrame (base : St) (_ : unit) (st : St) : Prop :=
  DFSFinishInv st /\
  visited1 base ⊆ visited1 st /\
  (forall x, visited1 base x -> finish st x = finish base x) /\
  visited2 st = visited2 base /\
  scc_id st = scc_id base /\
  scc_next st = scc_next base.

(** Local inductive for forward reachability — avoids SetsClass shadowing
    of clos_refl_trans.  rf_step extends on the RIGHT so that structural
    recursion decomposes from the end, matching Hneigh's one-step backward
    reasoning. *)
Inductive reach_fwd (v : V) : V -> Prop :=
| rf_refl : reach_fwd v v
| rf_step z w : reach_fwd v z -> step g z w -> reach_fwd v w.

Definition DFS_finish_f
           (W: V -> MonadErr.M St unit)
           (u: V): MonadErr.M St unit :=
  visit1 u;;
  repeat_break
    (fun e_set =>
       choice
        (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun st => ~ visited1 st v);;
           assume (fun _ => step_aux g e v u);;
           pre <- get (fun st pre => pre = st);;
           W v;;
           assertS (fun st =>
             DFSFinishInv st /\ visited1 st v /\ visited1 pre ⊆ visited1 st);;
           continue (e_set ∪ Sets.singleton e))
        (assume (fun st =>
                     forall (e:E) (v:V),
                      step_aux g e v u ->
                      e ∈ e_set \/ visited1 st v);;
          assertS (fun st => DFSFinishInv st);;
          assertS (fun st => timer st = cardV (fun v => finish st v <> 0));;
          t <- get (fun st t => t = timer st);;
          set_finish u t;;
          break tt))
    ∅.

Definition DFS_finish (u: V): MonadErr.M St unit :=
  BW_fix (DFS_finish_f) u.

(* ================================================================= *)
(* Inner DFS — Phase 2 (original graph, assign SCC root)             *)
(* ================================================================= *)

Definition DFS_scc_f
           (root: V)
           (W: V -> MonadErr.M St unit)
           (u: V): MonadErr.M St unit :=
  visit2 u;;
  set_scc_id u root;;
  repeat_break
    (fun e_set =>
       choice
         (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun st => ~ visited2 st v);;
          assume (fun _ => step_aux g e u v);;
          W v;;
          continue (e_set ∪ Sets.singleton e))
         (assume (fun st =>
                    forall (e:E) (v:V),
                      step_aux g e u v ->
                      e ∈ e_set \/ visited2 st v);;
          (* sid-stability assertS: at loop break, u's scc_id equals root's.
             Conveyed to the C refinement via Hoare_assertS_bind / safeExec,
             so the C-side dfs2 return witness can discharge sid-stability
             sampling subgoals without a forall in the loop invariant. *)
          assertS (fun st => scc_id st u = scc_id st root);;
          break tt))
    ∅.

Definition DFS_scc (root u: V): MonadErr.M St unit :=
  BW_fix (DFS_scc_f root) u.

(* ================================================================= *)
(* Pick an unvisited vertex with maximal finish number               *)
(* ================================================================= *)

Definition pick_unvisited1 : MonadErr.M St V :=
  get (fun st v => vvalid g v /\ ~ visited1 st v).

Definition pick_unvisited2 : MonadErr.M St V :=
  get (fun st v =>
    vvalid g v /\
    ~ visited2 st v /\
    forall w, ~ visited2 st w -> finish st v >= finish st w).

(* ================================================================= *)
(* Full Kosaraju algorithm                                           *)
(* ================================================================= *)

Definition kosaraju_finish_f
           (W: unit -> MonadErr.M St unit)
           (u: unit): MonadErr.M St unit :=
  choice
    (u <- pick_unvisited1;;
     DFS_finish u;;
     W tt)
    (assume (fun st => forall v, visited1 st v);;
     skip).

Definition kosaraju_finish : MonadErr.M St unit :=
  BW_fix kosaraju_finish_f tt.

Fixpoint kosaraju_finish_schedule_iter
         (root_at : nat -> V) (idx fuel : nat) : MonadErr.M St unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      let root := root_at idx in
      if_else (fun st => visited1 st root)
        (kosaraju_finish_schedule_iter root_at (S idx) fuel')
        (DFS_finish root;;
         kosaraju_finish_schedule_iter root_at (S idx) fuel')
  end.

Definition kosaraju_finish_schedule
           (root_at : nat -> V) (start fuel : nat) : MonadErr.M St unit :=
  kosaraju_finish_schedule_iter root_at start fuel.

Definition kosaraju_scc_f
           (W: unit -> MonadErr.M St unit)
           (u: unit): MonadErr.M St unit :=
  choice
    (u <- pick_unvisited2;;
     set_scc_root_id u;;
     DFS_scc u u;;
     W tt)
    (assume (fun st => forall v, visited2 st v);;
     skip).

Definition kosaraju_scc : MonadErr.M St unit :=
  BW_fix kosaraju_scc_f tt.

Fixpoint kosaraju_scc_schedule_iter
         (root_at : nat -> V) (idx fuel : nat) : MonadErr.M St unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      let root := root_at idx in
      if_else (fun st => visited2 st root)
        (kosaraju_scc_schedule_iter root_at (S idx) fuel')
        (visit2 root;;
         set_scc_id root root;;
         DFS_scc root root;;
         kosaraju_scc_schedule_iter root_at (S idx) fuel')
  end.

Definition kosaraju_scc_schedule
           (root_at : nat -> V) (start fuel : nat) : MonadErr.M St unit :=
  kosaraju_scc_schedule_iter root_at start fuel.

Definition kosaraju : MonadErr.M St unit :=
  kosaraju_finish;; kosaraju_scc.

(* ================================================================= *)
(* 0. Hoare Helper Theorems (from C10909)                            *)
(* ================================================================= *)

(** Lifts a pointwise Hoare triple to a general precondition P. *)

(** If P holds at s0, then assume P;; f has the Hoare triple for
    singleton precondition s = s0. Used for assume-guard elimination. *)

(** BW_fix induction principle: if f W a satisfies Q a s0 under the
    hypothesis that W a does, then BW_fix f a also satisfies Q a s0. *)

(** BW_fix induction with an invariant R closed under the recursive step.
    Variant of Hoare_normal_LFix carrying an extra hypothesis R s0. *)

(* ================================================================= *)
(* 1. Helper Hoare Lemmas for State Primitives                       *)
(* ================================================================= *)

(** visit1 u adds u to visited1; all other fields unchanged.
    Proved property: visited1 s' == visited1 s0 ∪ {u} *)

(** visit2 u adds u to visited2; all other fields unchanged.
    Proved property: visited2 s' == visited2 s0 ∪ {u} *)

(** get timer then set_finish u t stores one plus the current timer as finish[u],
    increments timer, and preserves finish for other vertices.
    Proved property: timer s' = S(timer s0) /\ finish s' u = S (timer s0) /\ ... *)

(* ================================================================= *)
(* 2. Inner DFS Phase 1 — Core Properties                            *)
(* ================================================================= *)

(** [DFS_finish_f_preserves_excess]: the single-unroll step underlying
    the timer/cardinality side condition. For any recursive body W that itself preserves
    the excess cardV(visited1) - timer (parameterised by k), DFS_finish_f W
    preserves it too. Factored out so that other Phase-1 fixpoint lemmas can
    reuse it as the "side" step in Hoare_BW_fix_logicv_conj'. *)

(** [DFS_finish_fixpoint_ind_strong]: a tailored fixpoint induction principle for
    Phase-1 property lemmas about [DFS_finish]. The step gets TWO induction
    hypotheses for the recursive body W: one for the (entry-state-indexed)
    property Q, and one for the k-parameterised excess (cardV - timer).
    The excess IH is what lets the step discharge the assertS timer-bound
    inside DFS_finish_f's break branch, while Q is free to mention the entry
    state s0 (so subset-style invariants carry). *)

(** Postcondition weakening: Hoare P f Q and Q -> R gives Hoare P f R. *)

(** visit1 preserves finish. Trivial but needed for set_finish reasoning.
    Proved property: finish s' = finish s0 *)

(** TimerDominates implies TimerDominates_except. Trivial weakening. *)

(** [DFS_finish_preserves_TimerDominates]
    DFS_finish u preserves the TimerDominates invariant (every visited1
    vertex has finish < timer), provided u was not already visited1.
    Proved property: TimerDominates s' *)

Definition Q_strict_new_finish (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  timer s0' <= timer s' /\
  (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' < finish s' v).

Definition R_non_closed (u : V) (st : St) : Prop :=
  forall v, visited1 st v ->
    ~ (forall w, step_rev v w -> visited1 st w) ->
    reachable_rev v u.

Definition ForwardReachClosed (s: St) : Prop :=
  forall v w, visited2 s v -> reachable g v w -> visited2 s w.

(** reachable_rev is transitive. *)

(** Combining two Hoare triples for the same program into a conjunction. *)

(** [finished_rev_to_root]
    Under ReachRevClosed s0' and visited1 s0' ⊆ visited1 st, if a is a
    non-root new vertex that has been finished (its subtree returned),
    b is not yet visited, and a can reachable_rev b, then the path
    a →* b must pass through the current DFS root u'.
    Uses ReachRevClosed s0' (not st) so it works at intermediate
    loop states where st may not be closed under reachable_rev. *)

(** [visited_boundary_not_closed]
    Purely set-theoretic: if [b] ∈ visited can reachable_rev some
    [c] ∉ visited, then the path [b →* c] must cross the boundary
    of [visited] at a vertex [v] ∈ visited that has a step_rev
    neighbour outside [visited] (hence [v] is not step_rev-closed).
    Moreover [reachable_rev b v]. *)

Definition ReachRevClosedEx (s: St) (x: V) : Prop :=
  forall v w, visited1 s v -> v <> x -> reachable_rev v w -> visited1 s w.

(** Phase 1 postcondition: if a can reverse-reach b but not vice versa,
    then a's SCC contains a vertex c whose finish exceeds b's finish.
    Encodes the condensation-DAG edge direction: larger finish values
    lie further "upstream" in the forward graph. *)
Definition Phase1_Order (s : St) : Prop :=
  forall a b, reachable_rev a b -> ~ reachable_rev b a ->
    exists c, mutually_reachable a c /\ finish s b < finish s c.

    
(* ================================================================= *)
(* 3. Outer Phase 1 — kosaraju_finish                                 *)
(* ================================================================= *)

(** [kosaraju_finish_visited_all_aux]
    Helper: if the remaining computation W visits all vertices, then one
    iteration of kosaraju_finish_f (pick unvisited, DFS_finish, recurse) also
    visits all vertices.
    Proved property: forall v, visited1 s' v *)

(** [kosaraju_finish_visited_all]
    After the full kosaraju_finish, all vertices are visited1.
    Proved property: forall v, visited1 s' v *)

(* ================================================================= *)
(* 3a. Inner Phase 1 — Phase1_Order for a single DFS tree             *)
(* ================================================================= *)

Definition Q_phase1 (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited1 s0' ⊆ visited1 s' /\
  visited1 s' u' /\
  (forall v w, visited1 s' v -> ~visited1 s0' v ->
               step_rev v w -> visited1 s' w) /\
  (forall v, visited1 s' v -> ~visited1 s0' v -> reachable_rev u' v) /\
  finish s' u' <= timer s' /\
  (forall z, visited1 s0' z -> z <> u' -> finish s' z = finish s0' z) /\
  timer s0' <= timer s' /\
  (forall v, v <> u' -> visited1 s' v ->
             visited1 s0' v \/ finish s' v < finish s' u') /\
  (forall v, visited1 s' v -> ~visited1 s0' v -> timer s0' <= finish s' v) /\
  (R_non_closed u' s0' -> R_non_closed u' s') /\
  (R_non_closed u' s0' ->
   forall a b,
     visited1 s' a -> ~visited1 s0' a ->
     visited1 s' b -> ~visited1 s0' b ->
     reachable_rev a b -> ~reachable_rev b a ->
     exists c, mutually_reachable a c /\ finish s' b < finish s' c).

Definition Phase1_R (s : St) : Prop :=
  ReachRevClosed s /\
  DFSFinishInv s /\
  (forall a b, visited1 s a -> visited1 s b ->
    reachable_rev a b -> ~ reachable_rev b a ->
    exists c, mutually_reachable a c /\ finish s b < finish s c).

(** Phase 1 establishes the condensation-DAG ordering: if a can
    reverse-reach b but not vice versa, then a's SCC contains a
    vertex with strictly larger finish than b's. *)

(* ================================================================= *)
(* 4. Inner DFS Phase 2 — Core Properties                            *)
(* ================================================================= *)

Definition neighbor_visited (st : St) (v : V) : Prop :=
  forall w, step g v w -> visited2 st w.

(** set_scc_id u root assigns scc_id[u] := scc_id[root]; other fields unchanged.
    Proved property: scc_id s' u = scc_id s0 root /\ ... *)

(** set_scc_root_id u assigns a fresh scc_id (scc_next) to u, then
    increments scc_next; other scc_id values unchanged.
    Proved property: scc_id s' u = scc_next s0 /\ scc_next s' = S(scc_next s0) /\ ... *)

Definition Q_scc_step_visited (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited2 s0' ⊆ visited2 s' /\
  visited2 s' u' /\
  (forall v, step g u' v -> visited2 s' v).

Definition DFSSccStable (root : V) (s0 st : St) : Prop :=
  scc_id st root = scc_id s0 root /\
  visited1 st = visited1 s0 /\
  finish st = finish s0 /\
  scc_next st = scc_next s0.

(** [DFS_scc_neighbor_visited_aux]
    Helper for the neighbor_visited invariant (forward graph analog of
    neighbor_visited_rev). Preserves visited2, subset, and neighbor_visited.
    Proved property: visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) *)

(** [DFS_scc_neighbor_visited_strong]
    Fixed-point version of neighbor_visited for DFS_scc.
    Proved property: visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) *)

(* SCC membership properties for Phase 2 correctness *)
(* L0a: all vertices newly visited by DFS_scc are reachable from u (the
   current vertex) in the original graph.  Direct mirror of
   DFS_finish_reachable_rev with step_rev replaced by step g. *)
(** [DFS_scc_reachable_aux]
    Helper: every newly visited2 vertex is reachable from u (forward graph)
    or was already in s0.
    Proved property: forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v *)

(** [DFS_scc_reachable_from_u]
    Fixed-point version: after DFS_scc root u, newly visited2 vertices are
    reachable from u in the original graph.
    Proved property: forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v *)

(** [DFS_scc_reachable]
    If root is reachable from root -> u, then DFS_scc root u ensures every
    newly visited2 vertex is reachable from root.
    Proved property: forall v, visited2 s' v -> ~visited2 s0 v -> reachable g root v *)

(** [DFS_scc_preserves_ForwardReachClosed]
    DFS_scc root u preserves the ForwardReachClosed invariant
    (visited2 is closed under forward reachability g),
    provided u was not already visited2.
    Proved property: ForwardReachClosed s' *)

(** [DFS_scc_reachable_visited_closed]
    Under ForwardReachClosed s0, DFS_scc root u visits every vertex
    reachable from u that was not already in visited2 s0.
    The closure condition ensures that the path from u to v contains
    no s0-vertex, so the DFS guard never blocks.
    Proved property: forall v, reachable g u v -> ~visited2 s0 v -> visited2 s' v *)

(** [mutually_reachable_from_order]
    Pure logic: if root can reach v, both are visited1, root has max finish
    among vertices not yet visited2, and v is not yet visited2, then
    root and v are mutually reachable.
    Proof: Phase1_Order gives exist c mutually-reachable v c with
    finish root < finish c; ForwardReachClosed + ~visited2 v forces
    ~visited2 c, then max-finish contradicts the strict inequality.
    Therefore reachable_rev root v must hold, giving mutually_reachable. *)

(** [DFS_scc_mutually_reachable_root]
    Under ForwardReachClosed, OrderInv, all-visited1, and max-finish,
    every vertex newly visited2 by DFS_scc root root is mutually reachable
    with root.
    Proved property: forall v, visited2 s' v -> ~visited2 s0 v -> mutually_reachable root v *)

(** [DFS_scc_visits_scc]
    Under ForwardReachClosed and max-finish, DFS_scc root root visits
    every vertex mutually reachable with root that is not already visited2.
    Proof: mutual → reachable, then DFS_scc_reachable_visited_closed.
    Proved property: forall v, mutually_reachable root v -> ~visited2 s0 v -> visited2 s' v *)

(* Every new vertex gets the same scc_id as root.
   Together with scc_next counter uniqueness, this gives:
   same scc_id → same SCC iteration → mutually reachable. *)
(** [DFS_scc_same_root_id]
    All newly visited2 vertices get the same scc_id as root,
    and scc_id of already-visited vertices is preserved. *)

(** [mutually_reachable_unvisited2]
    If root has max finish among unvisited vertices and is itself unvisited,
    then any vertex mutually reachable with root is also unvisited.
    Proof: if v were visited2 and reachable back to root, ForwardReachClosed
    would force root ∈ visited2, contradiction. *)

(** [DFS_scc_new_mutually_reachable]
    All vertices newly visited by DFS_scc root root are mutually reachable
    with each other.  Follows from DFS_scc_mutually_reachable_root
    (new → mutually reachable with root) and mutually_reachable_trans/sym.
    Proved property: forall u v, visited2 s' u -> visited2 s' v ->
      ~visited2 s0 u -> ~visited2 s0 v -> mutually_reachable u v *)

(** The invariant R(s) maintained by kosaraju_scc:
    - ForwardReachClosed: no forward edge crosses visited2 boundary
    - Phase1_Order: condensation-DAG finish ordering (immutable in Phase 2)
    - visited1-all: every vertex has been visited1 (immutable)
    - scc_id < scc_next: visited2 scc_ids from past rounds
    - correctness: scc_id equality iff mutually reachable within visited2 *)
Definition R (s : St) : Prop :=
  ForwardReachClosed s /\
  Phase1_Order s /\
  (forall v, visited1 s v) /\
  (forall v, visited2 s v -> scc_id s v < scc_next s) /\
  (forall u v, visited2 s u -> visited2 s v ->
    (scc_id s u = scc_id s v <-> mutually_reachable u v)).

(* ================================================================= *)
(* 5. Outer Phase 2 — kosaraju_scc                                    *)
(* ================================================================= *)

(** [kosaraju_scc_all_visited_aux]
    Helper: one iteration of kosaraju_scc_f visits all vertices in visited2.
    Proved property: forall v, visited2 s' v *)

(** [kosaraju_scc_all_visited]
    After the full kosaraju_scc, all vertices are visited2.
    Proved property: forall v, visited2 s' v *)

(** [kosaraju_scc_preserves_ForwardReachClosed]
    The outer loop kosaraju_scc preserves ForwardReachClosed.
    Each round: set_scc_root_id touches neither visited2 nor visited1;
    DFS_scc preserves it (DFS_scc_preserves_ForwardReachClosed).
    Proved property: ForwardReachClosed s' *)

Definition AntiTopo (s : St) : Prop :=
  forall a b, visited2 s a -> visited2 s b ->
    reachable_rev a b -> ~reachable_rev b a ->
    scc_id s a < scc_id s b.

(* ================================================================= *)
(* mono_cont + BW_fix unfold lemmas for DFS_finish_f / DFS_scc_f.       *)
(* These let the cursor continuations in the refinement lib relate    *)
(* dfs_finish_from/dfs_scc_from to the abstract DFS step behaviour.   *)
(* Mirrors DFS.DFS_mono_cont / DFS_unfold in algorithms/DFS/DFS.v.    *)
(* ================================================================= *)

(** [mono_cont_at]: if [f] is mono_cont as a function producing a
    pointwise-included value (codomain [C -> program Σ B]), then for any
    fixed [a : C] the specialisation [fun W => f W a] is also mono_cont.
    This bridges the gap left by [mono_cont_auto], which does not descend
    through applications of an [BW_fix]-producing function to a concrete
    argument (the [repeat_break (...) ∅] shape in DFS_finish_f). *)

(** [DFS_scc_absorb] — no-op transition.  When DFS_scc root u is started from
    a state where u is visited2, all of u's forward out-neighbours are
    visited2, and [scc_id st u = scc_id st root], then [DFS_scc root u] may
    take the no-op transition (tt, st): visit2 u and set_scc_id are absorbed
    (idempotent / already-set), and the repeat_break immediately breaks.  The
    sid-equality is exactly the [assertS (scc_id st u = scc_id st root)] guard
    that was added to DFS_scc_f's break branch — so the absorb is now
    contingent on the same fact the assertS checks.
    This is the engine for closing the dfs2 loop-exit / visited-skip gaps on
    the C-refinement side (lib: dfs_scc_absorb / dfs_scc_safe_return /
    dfs2_return_close).  *)

End Kosaraju.
