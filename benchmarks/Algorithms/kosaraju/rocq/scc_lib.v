Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Arith.
Require Import Lia.

Local Open Scope sets.

Section SCC.

Context {G V E: Type}
        (g: G)
        `{pg: Graph G V E}
        `{gv: GValid G}
        `{stepvalid: StepValid G V E}.

(* ================================================================= *)
(* 1. Mutually Reachable                                             *)
(* ================================================================= *)

Definition mutually_reachable (u v: V) : Prop :=
  reachable g u v /\ reachable g v u.

(* ================================================================= *)
(* 2. Strongly Connected Component                                   *)
(* ================================================================= *)

Definition is_SCC (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable u v) /\
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v).

(* ================================================================= *)
(* 3. SCC Partition                                                  *)
(* ================================================================= *)

Definition scc_partition (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).

Context {finitegraph: FiniteGraph G V E}.
Context {Hgvalid: gvalid g}.

Definition equiv_class (v: V) : V -> Prop :=
  fun w => vvalid g w /\ mutually_reachable v w.

(* ================================================================= *)
(* 4. Condensation DAG Acyclicity                                    *)
(* ================================================================= *)

Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step g u v.

Inductive condensation_reachable (sccs: list (V -> Prop)) : (V -> Prop) -> (V -> Prop) -> Prop :=
| cr_edge : forall s1 s2,
    condensation_edge sccs s1 s2 ->
    condensation_reachable sccs s1 s2
| cr_trans : forall s1 s2 s3,
    condensation_reachable sccs s1 s2 ->
    condensation_reachable sccs s2 s3 ->
    condensation_reachable sccs s1 s3.

(* ================================================================= *)
(* 5. Reversed Graph Reachability (for Kosaraju)                     *)
(* ================================================================= *)

Definition step_rev (x y: V) : Prop :=
  step g y x.

Definition reachable_rev (x y: V) : Prop := reachable g y x.

Definition mutually_reachable_rev (u v: V) : Prop :=
  reachable_rev u v /\ reachable_rev v u.

(* ================================================================= *)
(* 6. Head and Tail SCCs in the Condensation DAG                     *)
(* ================================================================= *)

Definition is_tail_SCC (sccs: list (V -> Prop)) (s: V -> Prop) : Prop :=
  In s sccs /\
  forall s', condensation_edge sccs s s' -> False.

Definition is_head_SCC (sccs: list (V -> Prop)) (s: V -> Prop) : Prop :=
  In s sccs /\
  forall s', condensation_edge sccs s' s -> False.

Definition condensation_edge_rev (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step_rev u v.

(* ================================================================= *)
(* 7. Topological Ordering of the Condensation DAG                    *)
(* ================================================================= *)

Definition is_SCC_list (l : list (V -> Prop)) : Prop :=
  forall s, In s l -> is_SCC s.

Definition condensation_acyclic_on (l : list (V -> Prop)) : Prop :=
  ~ exists s1 s2, condensation_edge l s1 s2 /\ condensation_reachable l s2 s1.

Fixpoint remove_one (sccs : list (V -> Prop)) (t : V -> Prop) : list (V -> Prop) :=
  match sccs with
  | nil => nil
  | s :: sccs' =>
      if excluded_middle_informative (s = t) then sccs'
      else s :: remove_one sccs' t
  end.

End SCC.

