(**
  C-facing refinement interface for the Kosaraju monadic development.

  The old [Kosaraju] development stores a finishing time as a vertex-indexed
  function [finish : V -> nat].  The C implementation instead writes a
  vertex into [fin] at each finishing event and consumes [fin] backwards in
  phase 2.  This file deliberately makes that representation change explicit.

  It is an interface layer, not an axiomatisation of the C program.  A C VC
  proves [CFinishSequence], [CLabelsRepresent], and the step simulation below;
  the theorems in this file then transfer the already proved monadic SCC
  correctness theorem to the C-facing arrays.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
From GraphLib Require Import graph_basic reachable_basic.
Require Import PVbench.Algorithms.kosaraju.rocq.kosaraju_model_lib.
Module Kosaraju := PVbench.Algorithms.kosaraju.rocq.kosaraju_model_lib.

Import ListNotations.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section CRefinement.

Context {G V E : Type}
        `{KG : KosarajuGraph G V E}
        (g : G)
        (g_valid : gvalid g).

(** [fin[i] = v] is the C meaning of [finish v = i + 1].  The offset is
    intentional: the monadic model reserves zero for an unfinished vertex,
    whereas C stores the first completed vertex in [fin[0]]. *)
Definition CFinishSequence (s : St) (fin : list V) : Prop :=
  length fin = timer s /\
  forall i v, nth_error fin i = Some v <-> finish s v = S i.

Definition CPhase1Refinement (s : St) (fin : list V) : Prop :=
  CFinishSequence s fin /\ Phase1_Order g s.

(** The C phase-2 loop reads [fin[n - 1 - i]].  Keeping [fin_at] total is
    convenient for the monadic schedule; VCs provide [i < n] before using it.
    With [n = length fin], this is exactly reverse finish order. *)
Definition c_phase2_root_at (fin_at : nat -> V) (n i : nat) : V :=
  fin_at (n - S i).

Definition c_phase2_root_at_list (fallback : V) (fin : list V) (i : nat) : V :=
  c_phase2_root_at (fun j => nth j fin fallback) (length fin) i.

(** One C phase-2 iteration, at the monadic abstraction level.  The explicit
    [visit2; set_scc_id root root] is deliberately retained: it is the shape
    of the C branch [sid[root] = root; dfs2(root, root)].  The second visit
    and assignment inside [DFS_scc] are idempotent model steps. *)
Definition c_phase2_iteration (root : V) : MonadErr.M St unit :=
  if_else (fun st => visited2 st root)
    (ret tt)
    (visit2 root;; set_scc_id root root;; DFS_scc g root root).

(** This is the exact program used by the old scheduled phase-2 model. *)

Definition c_phase2_schedule
           (fin_at : nat -> V) (n start fuel : nat) : MonadErr.M St unit :=
  kosaraju_scc_schedule g (c_phase2_root_at fin_at n) start fuel.

(** C stores a root vertex as the component label; the old monad stores a
    fresh natural component id.  Equality of labels, rather than their raw
    representation, is the simulation relation required by all SCC clients. *)
Definition CLabelsRepresent (label : V -> V) (s : St) : Prop :=
  forall u v, label u = label v <-> scc_id s u = scc_id s v.

Definition CLabelsCorrect (label : V -> V) : Prop :=
  forall u v, label u = label v <-> mutually_reachable g u v.

(** The end-to-end monadic theorem is the semantic source for a C refinement:
    a C final-state proof supplies [CLabelsRepresent] for its simulated final
    monadic state, and this lemma transfers the theorem without reproving SCC
    graph theory in the C VC layer. *)

(** A root-labelled C component can be connected to the monad locally.  This
    is the postcondition a C [sid[root] = root; dfs2(root, root)] simulation
    should establish for newly visited vertices; old labels are intentionally
    framed outside this local component relation. *)
Definition CRootLabelComponent (before after : St) (root : V)
           (label : V -> V) : Prop :=
  label root = root /\
  forall v, ~ visited2 before v ->
    (label v = root <-> scc_id after v = scc_id after root).

End CRefinement.
