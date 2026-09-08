(** * A concrete rooted tree: [RootedTreeType], lifted out of Tarjan.

    [GraphLib/directed/rootedtree.v] develops rooted trees abstractly --
    parent uniqueness, the ancestor partial order, and the two structural
    induction principles [rooted_tree_induction_bottom_up] and
    [rooted_tree_induction_top_down] -- entirely under [Context] hypotheses
    [Forest] and [RootedTree].  The only place in the repository that
    discharges those is [GraphLib/examples/tarjan.v], on the record it builds
    for a DFS tree.  Nothing about that record is specific to Tarjan: it is a
    rooted tree given by a parent function, generic in [V] and [E], and it is
    exactly what a solver's [par[]] array is.

    It cannot be reached by importing [tarjan.v].  That file pulls in
    [dfstree] and [subgraph], hence [epath], and [epath.vo] is stale against
    [path.vo]; and [Makefile.codeforces] puts GraphLib on the load path
    without building it, so a benchmark proof cannot rely on a GraphLib
    rebuild having happened.  The declarations below are therefore lifted
    verbatim from [tarjan.v] lines 103-347 -- the block ending just before
    [Section TARJAN], which is where the DFS-specific development starts.
    They need only [graph_basic], [reachable_basic], [reachable_restricted]
    and [rootedtree]; the extraction was checked to compile with exactly
    those.

    This file is a copy, and copies drift.  If GraphLib ever hoists this block
    into [directed/] itself, delete this file and import that instead.  The
    distance results built on top of it live in [RootedTreeDistance.v] and are
    stated generically, so they survive such a move unchanged. *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted rootedtree.



Record RootedTreeType {V E: Type}:=
{
  vset: V -> Prop;
  theroot: V;
  parent: V -> V;
  edge: V -> option E;
  listV: list V;
}.

Arguments RootedTreeType _ _ : clear implicits.

Notation "tree '.(vset)'" := (vset tree) (at level 1).
Notation "tree '.(root)'" := (theroot tree) (at level 1).
Notation "tree '.(parent)'" := (parent tree) (at level 1).
Notation "tree '.(edge)'" := (edge tree) (at level 1).

Record RootedTreeProp {V E: Type} (rt: RootedTreeType V E):=
{
  root_no_edge: rt.(edge) (rt.(root)) = None;
  edge_some: forall v, rt.(vset) v -> v <> rt.(root) -> exists e, rt.(edge) v = Some e;
  edge_unique: forall v1 v2, rt.(vset) v1 -> rt.(vset) v2 -> rt.(edge) v1 = rt.(edge) v2 -> v1 = v2;
  root_valid: rt.(vset) rt.(theroot);
  parent_valid: forall v, rt.(vset) v -> rt.(vset) (rt.(parent) v);
  path_exist: forall v, rt.(vset) v -> clos_refl_trans (fun x y => rt.(parent) y = x) rt.(theroot) v;
  finite_vertices: forall v, rt.(vset) v -> In v rt.(listV) ;
}.

Arguments RootedTreeProp _ _ : clear implicits.

Definition rt_vvalid {V E: Type} (g: RootedTreeType V E) (v: V): Prop :=
  g.(vset) v.

Definition rt_evalid {V E: Type} (g: RootedTreeType V E) (e: E): Prop :=
  exists v, g.(vset) v /\ g.(edge) v = Some e.

Record rt_step_aux {V E: Type} (g: RootedTreeType V E) (e: E) (x y: V): Prop := 
{ 
  vx : g.(vset) x;
  vy : g.(vset) y;
  ve : g.(edge) y = Some e;
  vp : g.(parent) y = x
}.

#[export]Program Instance Rootedtree_graph {V E: Type}:
  graph_basic.Graph (RootedTreeType V E) V E := {
  vvalid := rt_vvalid ;
  evalid := rt_evalid ;
  step_aux := rt_step_aux;
}.

#[export]Instance Rootedtree_gvalid {V E: Type}:
  graph_basic.GValid (RootedTreeType V E) :=
  @RootedTreeProp V E.

#[export]Instance Rootedtree_stepvalid {V E: Type}: 
  StepValid (RootedTreeType V E) V E.
Proof.
  split; intros; destruct H; auto.
  exists y; auto.
Qed. 

#[export]Instance Rootedtree_noemptyedge {V E: Type} : 
  graph_basic.NoEmptyEdge (RootedTreeType V E) V E.
Proof.
  split; intros.
  destruct H0 as [v [? ?]].
  exists (parent g v), v; repeat split; auto.
  apply parent_valid; auto.
Qed.

#[export]Instance Rootedtree_directedgragh {V E: Type}: 
  graph_basic.StepUniqueDirected (RootedTreeType V E) V E .
Proof.
  split; intros ? ? ? ? ? ? HH ? ?.
  destruct H.
  destruct H0.
  rewrite <- ve0 in ve1.
  eapply edge_unique in ve1; eauto. 
  subst y2.
  rewrite <- vp1; subst x2.
  split; auto.
Qed.

#[export]Instance RootedTree_finitegraph {V E: Type}:
  graph_basic.FiniteGraph (RootedTreeType V E) V E. 
Proof.
  refine {|graph_basic.listV:= listV;|}.
  intros; apply finite_vertices; auto.
Defined.

#[export]Instance Rootedtree_forest {V E: Type}:
  Forest (RootedTreeType V E) V E.
Proof.
  split.
  - intros g x1 x2 e1 e2 y HH H1 H2.
    destruct H1 as [_ _ H1 _].
    destruct H2 as [_ _ H2 _].
    rewrite H1 in H2. 
    inversion H2; auto. 
  - intros g x y HH Hxy Hyx.
    assert (Hfather_vunique: forall x1 x2 y,
      step g x1 y -> step g x2 y -> x1 = x2).
    {
      intros x1 x2 y0 H1 H2.
      destruct H1 as [e1 H1].
      destruct H2 as [e2 H2].
      destruct H1 as [_ _ _ Hparent1].
      destruct H2 as [_ _ _ Hparent2].
      rewrite <- Hparent1, <- Hparent2; auto.
    }
    assert (Hroot_is_root: forall x0,
      vvalid g x0 -> reachable g (g.(root)) x0).
    {
      intros x0 Hvalid.
      apply path_exist in Hvalid as H0; auto.
      revert Hvalid; rename H0 into Hpath.
      remember g.(root) as r.
      induction_n1 Hpath.
      - reflexivity.
      - destruct (classic (x0 = r)).
        + subst x0; reflexivity.
        + eapply parent_valid in Hvalid as Hparent_valid; eauto.
          rewrite H in Hparent_valid.
          apply IHrt in Hparent_valid as Hreach; auto.
          etransitivity; eauto.
          unfold reachable.
          apply step_rt.
          apply edge_some in Hvalid as Hedge; auto.
          destruct Hedge as [e Hedge].
          exists e; repeat split; auto.
          subst r; auto.
    }
    assert (Hroot_no_father: forall x0, ~ step g x0 g.(root)).
    {
      intros x0 Hstep.
      destruct Hstep as [e Hstep].
      destruct Hstep as [_ _ Hedge _].
      erewrite root_no_edge in Hedge; eauto.
      inversion Hedge.
    }
    assert (Hone_reachable_down_up: forall x0 y0 z,
      reachable g x0 z -> step g y0 z -> x0 <> z -> reachable g x0 y0).
    {
      intros x0 y0 z Hreach Hstep Hneq.
      unfold reachable in Hreach.
      induction_n1 Hreach.
      - exfalso; apply Hneq; trivial.
      - match goal with
        | Hlast : step g ?p z |- _ =>
            assert (p = y0) as Heq
              by (eapply Hfather_vunique; [exact Hlast | exact Hstep]);
            subst p;
            unfold reachable; exact Hreach
        end.
    }
    assert (Hpartial_order: forall x0 y0,
      reachable g x0 y0 -> reachable g y0 x0 -> x0 = y0).
    {
      intros x0 y0 Hxy0 Hyx0.
      destruct (classic (x0 = y0)); auto.
      pose proof Hxy0 as Hxy0_valid.
      eapply reachable_vvalid in Hxy0_valid as [Hxvalid _]; eauto.
      apply Hroot_is_root in Hxvalid as Hroot_path; auto.
      clear Hxvalid H.
      revert y0 Hxy0 Hyx0.
      unfold reachable in Hroot_path.
      remember g.(root) as r.
      induction_n1 Hroot_path; intros; auto.
      - unfold reachable in Hyx0.
        induction_n1 Hyx0; subst; auto.
        exfalso.
        eapply Hroot_no_father; eauto.
      - destruct (classic (x0 = y0)).
        + subst; auto.
        + eapply Hone_reachable_down_up in Hyx0 as Hup; eauto.
          eapply step_reachable_reachable in H as Hdown; eauto.
          eapply IHrt in Hup; eauto.
          subst r0. symmetry.
          eapply IHrt; eauto.
    }
    assert (Hno_edge_refl: forall x0 y0,
      step g x0 y0 -> ~ step g y0 x0).
    {
      intros x0 y0 Hstep Hback.
      pose proof Hstep as Hstep_valid.
      destruct Hstep_valid as [e Hstep_aux].
      eapply step_vvalid1 in Hstep_aux as Hxvalid; eauto.
      apply Hroot_is_root in Hxvalid as Hroot_path; auto.
      clear e Hstep_aux Hxvalid.
      revert y0 Hstep Hback.
      unfold reachable in Hroot_path.
      remember g.(root) as r.
      induction_n1 Hroot_path; intros.
      - eapply Hroot_no_father; eauto.
      - eapply Hfather_vunique in H; eauto.
        subst y0.
        eapply IHrt; eauto.
    }
    destruct (classic (x = y)).
    + subst y.
      eapply Hno_edge_refl; eauto.
    + apply H.
      eapply Hpartial_order; eauto.
      apply step_rt; auto.
Qed.
  
#[export]Instance Rootedtree_prop {V E: Type} :
  RootedTree (RootedTreeType V E) V E.
Proof.
  refine {|root := theroot;|}.
  - intros; apply root_valid; auto.
  - intros g x HH H.
  apply path_exist in H as H0; auto. 
  revert H; rename H0 into H.
  remember g.(root) as r. 
  induction_n1 H. 
  reflexivity.
  destruct (classic (x = r)).
  subst x; reflexivity.
  eapply parent_valid in H0 as Hy.
  rewrite H1 in Hy.
  apply IHrt in Hy as ?; auto.
  etransitivity; eauto.
  unfold reachable.
  apply step_rt.
  apply edge_some in H0 as H4; auto.
  destruct H4 as [e H4].
  exists e; repeat split; auto.
  subst r; auto.
  auto. 
Defined.


#[export]Instance simple_graph{V E: Type}: 
  graph_basic.SimpleGraph (RootedTreeType V E) V E.
Proof.
  split; intros.
  - eapply father_eunique; eauto.
  - unfold not; intros H0.
    apply step_trivial in H0.
    eapply no_edge_refl; eauto.
    Unshelve. auto.
Qed.
