(** * Depth in a rooted tree.

    [GraphDistanceZ] gives [zdistance], the least walk length, over any
    [Graph G V E].  [rootedtree.v] gives the structure of a rooted tree but
    says nothing about distance.  This file joins them: in a rooted tree the
    *minimal* walk length to a vertex is its parent's plus one, because every
    walk into a vertex arrives through that vertex's unique parent.  That is
    the recurrence a breadth-first search writes as [depth[v] = depth[u] + 1],
    and it is the obligation a BFS loop invariant discharges.

    Everything is stated over an abstract rooted tree -- [Forest] and
    [RootedTree] as hypotheses -- so it applies to [RootedTreeType] from
    [RootedTreeInstances.v], and to any other concrete rooted tree added
    later, without change. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic rootedtree.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphDistanceZ.
Require Import SimpleC.EE.LLM_bench.Codeforces.RootedTreeInstances.

Import ListNotations.

Local Open Scope Z_scope.

Section ROOTED_DISTANCE.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        {forest: Forest G V E}
        {rooted: RootedTree G V E}
        (g: G)
        (g_valid: gvalid g).

Notation r := (root g).

(** No edge enters the root: the root reaches every vertex, and a forest has
    no edge running back along reachability. *)
Lemma rooted_no_step_to_root : forall x, ~ step g x r.
Proof.
  intros x Hs.
  assert (Hv : vvalid g x) by (destruct Hs as [e He]; eapply step_vvalid1; eauto).
  exact (no_reachable_back_edge g r x g_valid (root_is_root g x g_valid Hv) Hs).
Qed.

(** Every walk from the root into [y] has length at least one and reaches
    [y]'s parent one step earlier -- [y]'s *only* parent, by [father_vunique],
    which is what makes the length exact rather than merely bounded. *)
Lemma rooted_path_pred : forall x y k,
  step g x y ->
  path_of_zlen g r y k ->
  exists j, k = j + 1 /\ path_of_zlen g r x j.
Proof.
  intros x y k Hstep Hpath.
  assert (Hk0 : 0 <= k) by (eapply path_of_zlen_nonneg; eauto).
  destruct (Z.eq_dec k 0) as [-> | Hne].
  { apply path_of_zlen_0_inv in Hpath. subst y.
    exfalso. exact (rooted_no_step_to_root x Hstep). }
  assert (Hk1 : 0 <= k - 1) by lia.
  destruct (path_of_zlen_succ_inv g r y k (k - 1) Hpath Hk1 ltac:(lia))
    as [w [Hw Hstepw]].
  exists (k - 1). split; [lia |].
  assert (w = x) as ->
    by (eapply (@father_vunique G V E pg gv stepvalid step_aux_unique forest g g_valid);
        eauto).
  exact Hw.
Qed.

(** The BFS recurrence. *)
Theorem rooted_depth_step : forall x y dx,
  step g x y ->
  zdistance g r x dx ->
  zdistance g r y (dx + 1).
Proof.
  intros x y dx Hstep Hdx.
  apply zdistance_iff in Hdx as [Hpx Hmin].
  apply zdistance_iff. split.
  - eapply pozl_step; eauto.
  - intros k Hk.
    destruct (rooted_path_pred x y k Hstep Hk) as [j [-> Hj]].
    specialize (Hmin j Hj). lia.
Qed.

(** Depth is defined everywhere: the root reaches every vertex. *)
Lemma rooted_depth_exists : forall x, vvalid g x -> exists d, zdistance g r x d.
Proof.
  intros x Hv. apply reachable_iff_zdistance.
  exact (root_is_root g x g_valid Hv).
Qed.

(** Depth is unique, so [zdistance g r x] behaves as the function a program
    stores in [depth[]]. *)
Lemma rooted_depth_unique : forall x d1 d2,
  zdistance g r x d1 -> zdistance g r x d2 -> d1 = d2.
Proof. intros. eapply zdistance_unique; eauto. Qed.

Lemma rooted_depth_root : zdistance g r r 0.
Proof. apply zdistance_refl. Qed.

End ROOTED_DISTANCE.

(** ** A witness

    [RootedTreeProp] is a conjunction of seven clauses over functions the
    caller supplies, so it is worth having on record that it is satisfiable
    and that the results above actually land on a concrete tree -- an
    unsatisfiable well-formedness condition would make every theorem here
    vacuously true.  The tree is [1 -> 2]. *)

Definition ExampleT2 : RootedTreeType Z Z :=
  {| vset := fun v => v = 1 \/ v = 2;
     theroot := 1;
     parent := fun _ => 1;
     edge := fun v => if Z.eqb v 2 then Some 0 else None;
     listV := [1; 2] |}.

Lemma ExampleT2_wf : RootedTreeProp Z Z ExampleT2.
Proof.
  constructor; simpl.
  - reflexivity.
  - intros v Hv Hne. destruct Hv as [-> | ->]; [contradiction | exists 0; reflexivity].
  - intros v1 v2 H1 H2 Heq.
    destruct H1 as [-> | ->]; destruct H2 as [-> | ->]; simpl in *; congruence.
  - left; reflexivity.
  - intros v _. left; reflexivity.
  - intros v Hv. destruct Hv as [-> | ->].
    + reflexivity.
    + transitivity_1n 2; [reflexivity | reflexivity].
  - intros v Hv. destruct Hv as [-> | ->]; simpl; auto.
Qed.

Lemma ExampleT2_step : step ExampleT2 1 2.
Proof. exists 0. constructor; simpl; auto. Qed.

(** The child sits at depth one, by [rooted_depth_step] and nothing else. *)
Lemma ExampleT2_depth : zdistance ExampleT2 (root ExampleT2) 2 1.
Proof.
  replace 1 with (0 + 1) by lia.
  eapply rooted_depth_step; [exact ExampleT2_wf | exact ExampleT2_step |].
  replace (root ExampleT2) with 1 by reflexivity.
  apply zdistance_refl.
Qed.
