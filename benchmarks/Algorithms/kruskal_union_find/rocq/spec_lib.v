Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
Require Import ListLib.Base.Positional.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

(** * Kruskal 边表版本的具体图模型 *)

Definition V : Type := Z.
Definition E : Type := Z.

Record G : Type := mkG {
  graph_from : E -> V;
  graph_to : E -> V;
  graph_weight : E -> Z;
  graph_vertices : list V;
  graph_edges : list E;
}.

Definition edge_src (g : G) (e : E) : V :=
  graph_from g e.

Definition edge_dst (g : G) (e : E) : V :=
  graph_to g e.

Definition graph_edge_count (g : G) : Z :=
  Zlength (graph_edges g).

Definition graph_vertex_count (g : G) : Z :=
  Zlength (graph_vertices g).

Definition edge_endpoints_valid (g : G) (e : E) : Prop :=
  In (edge_src g e) (graph_vertices g) /\
  In (edge_dst g e) (graph_vertices g).

Definition graph_step (g : G) (e : E) (u v : V) : Prop :=
  In e (graph_edges g) /\
  edge_endpoints_valid g e /\
  ((u = edge_src g e /\ v = edge_dst g e) \/
   (u = edge_dst g e /\ v = edge_src g e)).

Definition graph_wf (g : G) : Prop :=
  forall e, In e (graph_edges g) -> exists u v, graph_step g e u v.

(** ** GraphLib 接口实例 *)

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := fun g v => In v (graph_vertices g);
  evalid := fun g e => In e (graph_edges g);
  step_aux := graph_step;
|}.

#[export] Instance gvalid_instance : GValid G := graph_wf.

#[export] Instance stepvalid_instance : StepValid G V E.
Proof.
  constructor.
  - intros g e x y Hstep.
    destruct Hstep as [_ [[Hsrc Hdst] Hends]].
    destruct Hends as [[-> ->] | [-> ->]]; auto.
  - intros g e x y Hstep.
    destruct Hstep as [_ [[Hsrc Hdst] Hends]].
    destruct Hends as [[-> ->] | [-> ->]]; auto.
  - intros g e x y Hstep.
    destruct Hstep as [He _]; exact He.
Qed.

#[export] Instance noempty_instance : NoEmptyEdge G V E.
Proof.
  constructor.
  intros g e Hg He.
  exact (Hg e He).
Qed.

#[export] Instance undirected_instance : UndirectedGraph G V E.
Proof.
  constructor.
  intros g e x y Hstep.
  destruct Hstep as [He [Hends [[Hx Hy] | [Hx Hy]]]]; subst.
  - split; [exact He | split; [exact Hends | right; auto]].
  - split; [exact He | split; [exact Hends | left; auto]].
Qed.

#[export] Instance stepunique_instance : StepUniqueUndirected G V E.
Proof.
  constructor.
  intros g e x1 y1 x2 y2 _ H1 H2.
  destruct H1 as [_ [_ Hxy1]].
  destruct H2 as [_ [_ Hxy2]].
  destruct Hxy1 as [[-> ->] | [-> ->]];
    destruct Hxy2 as [[-> ->] | [-> ->]]; auto.
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := graph_vertices |}.
  intros g _ v Hv; exact Hv.
Qed.

#[export] Instance finiteE_instance : FiniteEGraph G V E.
Proof.
  refine {| listE := graph_edges |}.
  intros g _ e He; exact He.
Qed.

Definition valid_edges (g : G) : list E :=
  nodup Z.eq_dec (graph_edges g).

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := valid_edges |}.
  - intros g _.
    unfold valid_edges.
    apply NoDup_nodup.
  - intros g _ e.
    unfold valid_edges.
    rewrite nodup_In.
    tauto.
Qed.

#[export] Instance edge_weight_instance : EdgeWeight G E := {|
  weight := fun g e => Some (graph_weight g e);
|}.

(** * 具体路径模型 *)

Record path: Type := mkpath {
  path_edges: list (E*V);
  path_start: V;
}.

Definition path_vertices (p : path) : list V :=
  path_start p :: map snd (path_edges p).

Definition path_edge_ids (p : path) : list E :=
  map fst (path_edges p).

Definition path_head (p : path) : V :=
  path_start p.

Definition path_tail (p : path) : V :=
  last (path_vertices p) 0.

Definition empty_path_impl (v : V) : path :=
  mkpath nil v.

Definition single_path_impl (u v : V) (e : E) : path :=
  mkpath ((e, v) :: nil) u.

Definition concat_path_impl (p q : path) : path :=
  mkpath (path_edges p ++ path_edges q) (path_start p).

Definition P : Type := path.

Definition path_valid_prop (g : G) (p : path) : Prop :=
  vpath_iff_epath_prop g (path_vertices p) (path_edge_ids p).

(** * 路径辅助引理 *)

Lemma path_vertices_nonempty :
  forall p, path_vertices p <> nil.
Proof.
  intros p.
  unfold path_vertices.
  destruct p; simpl; discriminate.
Qed.

Lemma path_tail_valid :
  forall p, Some (path_tail p) = tl_error (path_vertices p).
Proof.
  intros p.
  unfold path_tail.
  pose proof (path_vertices_nonempty p) as Hnonempty.
  apply exists_last in Hnonempty as [prefix [x Hx]].
  rewrite Hx.
  rewrite tl_error_last.
  rewrite last_last.
  reflexivity.
Qed.

Lemma nth_error_path_vertices_last :
  forall (s : V) (es : list (E * V)),
    nth_error (s :: map snd es) (length es) =
    Some (last (s :: map snd es) 0).
Proof.
  intros s es.
  revert s.
  induction es as [| [e v] es IH]; intros s; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma nth_error_concat_vertices_boundary_app :
  forall (s1 : V) (es1 : list (E * V)) (s2 : V) (es2 : list (E * V)),
    last (s1 :: map snd es1) 0 = s2 ->
    nth_error ((s1 :: map snd es1) ++ map snd es2) (length es1) =
    nth_error (s2 :: map snd es2) 0.
Proof.
  intros s1 es1 s2 es2 Htail.
  rewrite nth_error_app1 by (simpl; rewrite length_map; lia).
  rewrite nth_error_path_vertices_last.
  rewrite Htail.
  reflexivity.
Qed.

Lemma nth_error_concat_vertices_after_app :
  forall (s1 : V) (es1 : list (E * V)) (s2 : V) (es2 : list (E * V)) k,
    nth_error ((s1 :: map snd es1) ++ map snd es2) (length es1 + S k) =
    nth_error (s2 :: map snd es2) (S k).
Proof.
  intros s1 es1 s2 es2 k.
  rewrite nth_error_app2 by (simpl; rewrite length_map; lia).
  replace (length es1 + S k - length (s1 :: map snd es1))%nat with k
    by (simpl; rewrite length_map; lia).
  reflexivity.
Qed.

(** * GraphLib 路径接口实例 *)

#[export] Instance path_instance : Path G V E P.
Proof.
  refine {|
    path_valid := path_valid_prop;
    vertex_in_path := path_vertices;
    head := path_head;
    head_valid := _;
    tail := path_tail;
    tail_valid := _;
    edge_in_path := path_edge_ids;
    vpath_iff_epath := _;
  |}.
  - intros g p Hvalid.
    unfold path_head, path_vertices.
    destruct p; reflexivity.
  - intros g p Hvalid.
    apply path_tail_valid.
  - intros g p Hvalid.
    exact Hvalid.
Defined.

#[export] Instance emptypath_instance :
  EmptyPath G V E P path_instance.
Proof.
  refine {|
    empty_path := empty_path_impl
  |}.
  - intros g v.
    split.
    + reflexivity.
    + intros n u w e Hn _ _ _.
      simpl in Hn; lia.
  - intros v; reflexivity.
Defined.

Lemma single_path_valid_impl :
  forall g u v e,
    step_aux g e u v ->
    path_valid g (single_path_impl u v e).
Proof.
  intros g u v e Hstep.
  unfold path_valid, path_instance, path_valid_prop,
    single_path_impl, path_vertices, path_edge_ids.
  simpl.
  split.
  - reflexivity.
  - intros n u' v' e' Hn He Hu Hv.
    destruct n as [| n]; [| simpl in Hn; lia].
    simpl in He, Hu, Hv.
    inversion He; inversion Hu; inversion Hv; subst.
    exact Hstep.
Qed.

#[export] Instance singlepath_instance :
  SinglePath G V E P path_instance.
Proof.
  refine {|
    single_path := single_path_impl;
    single_path_valid := single_path_valid_impl;
    single_path_vertex := _;
    single_path_edge := _;
  |}.
  - intros u v e; reflexivity.
  - intros u v e; reflexivity.
Defined.

Lemma concat_path_valid_impl :
  forall g a1 a2,
    path_valid g a1 ->
    path_valid g a2 ->
    tail a1 = head a2 ->
    path_valid g (concat_path_impl a1 a2).
Proof.
  intros g [es1 s1] [es2 s2] Hvalid1 Hvalid2 Hjoin.
  unfold path_valid, path_instance, path_valid_prop,
    concat_path_impl, path_vertices, path_edge_ids, path_tail, path_head
    in Hvalid1, Hvalid2, Hjoin |- *.
  simpl in Hvalid1, Hvalid2, Hjoin |- *.
  destruct Hvalid1 as [_ Hstep1].
  destruct Hvalid2 as [_ Hstep2].
  split.
  - simpl.
    repeat rewrite length_map.
    lia.
  - intros n u v e Hn He Hu Hv.
    rewrite map_app in He.
    rewrite map_app in Hu, Hv.
    change (s1 :: map snd es1 ++ map snd es2)
      with ((s1 :: map snd es1) ++ map snd es2) in Hu.
    change (s1 :: map snd es1 ++ map snd es2)
      with ((s1 :: map snd es1) ++ map snd es2) in Hv.
    destruct (lt_dec n (length es1)) as [Hleft | Hright].
    + eapply Hstep1.
      * split; [lia | rewrite length_map; exact Hleft].
      * rewrite nth_error_app1 in He by (rewrite length_map; exact Hleft).
        exact He.
      * rewrite nth_error_app1 in Hu by (simpl; rewrite length_map; lia).
        exact Hu.
      * rewrite nth_error_app1 in Hv by (simpl; rewrite length_map; lia).
        exact Hv.
    + pose (k := (n - length es1)%nat).
      assert (Hn_eq : n = (length es1 + k)%nat) by (unfold k; lia).
      replace n with (length es1 + k)%nat in * by (symmetry; exact Hn_eq).
      rewrite nth_error_app2 in He by (rewrite length_map; lia).
      replace (length es1 + k - length (map fst es1))%nat with k in He
        by (rewrite length_map; lia).
      destruct k as [| k].
      * eapply Hstep2.
        -- split; [lia | apply nth_error_Some; rewrite He; discriminate].
        -- exact He.
        -- replace (length es1 + 0)%nat with (length es1) in Hu by lia.
           rewrite (nth_error_concat_vertices_boundary_app s1 es1 s2 es2 Hjoin) in Hu.
           exact Hu.
        -- replace (S (length es1 + 0))%nat with (length es1 + S 0)%nat in Hv by lia.
           rewrite (nth_error_concat_vertices_after_app s1 es1 s2 es2 0) in Hv.
           exact Hv.
      * eapply Hstep2.
        -- split; [lia | apply nth_error_Some; rewrite He; discriminate].
        -- exact He.
        -- rewrite (nth_error_concat_vertices_after_app s1 es1 s2 es2 k) in Hu.
           exact Hu.
        -- replace (S (length es1 + S k))%nat with (length es1 + S (S k))%nat in Hv by lia.
           rewrite (nth_error_concat_vertices_after_app s1 es1 s2 es2 (S k)) in Hv.
           exact Hv.
Qed.

#[export] Instance concatpath_instance :
  ConcatPath G V E P path_instance.
Proof.
  refine {|
    concat_path := concat_path_impl;
    concat_path_valid := concat_path_valid_impl;
    concat_path_vertex := _;
    concat_path_edge := _;
  |}.
  - intros a1 a2.
    unfold concat_path_impl, path_vertices.
    destruct a1 as [es1 s1], a2 as [es2 s2].
    change (s1 :: map snd (es1 ++ es2) =
      (s1 :: map snd es1) ++ map snd es2).
    rewrite map_app.
    reflexivity.
  - intros a1 a2.
    unfold concat_path_impl, path_edge_ids.
    destruct a1 as [es1 s1], a2 as [es2 s2].
    change (map fst (es1 ++ es2) = map fst es1 ++ map fst es2).
    rewrite map_app.
    reflexivity.
Defined.

#[export] Instance destruct1npath_instance :
  Destruct1nPath G V E P path_instance
    emptypath_instance singlepath_instance concatpath_instance.
Proof.
  unshelve econstructor.
  - intros g [es s] Hvalid.
    destruct es as [| [e v] es].
    + exact (DestructBase1n s).
    + exact (DestructStep1n (mkpath es v) s v e).
  - intros g [es s] Hvalid.
    unfold path_cons_spec.
    destruct es as [| [e v] es].
    + reflexivity.
    + simpl.
      unfold path_valid, path_instance, path_valid_prop,
        path_vertices, path_edge_ids, path_head in Hvalid |- *.
      simpl in Hvalid |- *.
      destruct Hvalid as [Hlen Hstep].
      split.
      * split.
        -- simpl in Hlen.
           simpl.
           repeat rewrite length_map in Hlen |- *.
           lia.
        -- intros i x y a Hi Ha Hu Hy.
           eapply Hstep with (n := S i).
           ++ simpl.
              repeat rewrite length_map in Hi |- *.
              lia.
           ++ simpl.
              exact Ha.
           ++ simpl.
              exact Hu.
           ++ simpl.
              exact Hy.
      * split.
        -- reflexivity.
        -- split.
           ++ eapply Hstep with (n := 0%nat).
              ** simpl.
                 repeat rewrite length_map.
                 lia.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
           ++ reflexivity.
Defined.
#[export] Instance tree_instance :
  @Tree G V E graph_instance gvalid_instance P path_instance.
Proof.
  refine {|
    tree := fun g =>
      connected g /\
      ~ exists u p, p <> nil /\ is_simple_epath g u p u
  |}.
  - intros g [Hconnected _]; exact Hconnected.
  - intros g [_ Hacyclic]; exact Hacyclic.
  - intros g Hconnected Hacyclic; split; auto.
Defined.

(** * 输入三数组到抽象图的绑定 *)

Definition array_graph
    (n m : Z) (from to wt : list Z) (g : G) : Prop :=
  graph_vertices g = Zrange 0 n /\
  graph_edges g = Zrange 0 m /\
  0 <= n /\
  0 <= m /\
  Zlength from = m /\
  Zlength to = m /\
  Zlength wt = m /\
  (forall e, In e (Zrange 0 m) ->
    graph_from g e = Znth e from 0 /\
    graph_to g e = Znth e to 0 /\
    graph_weight g e = Znth e wt 0).

Definition uf_domain (n : Z) (x : Z) : Prop :=
  0 <= x < n.

Definition add_edge_graph (g : G) (u v : V) (e : E) : G :=
  mkG
    (fun a => if Z.eq_dec a e then u else graph_from g a)
    (fun a => if Z.eq_dec a e then v else graph_to g a)
    (graph_weight g)
    (u :: v :: graph_vertices g)
    (e :: graph_edges g).

Definition remove_edge_graph (g : G) (e : E) : G :=
  mkG
    (graph_from g)
    (graph_to g)
    (graph_weight g)
    (graph_vertices g)
    (filter (fun a => if Z.eq_dec a e then false else true) (graph_edges g)).

Lemma add_edge_graph_vvalid :
  forall g u v e x,
    vvalid (add_edge_graph g u v e) x <-> vvalid g x \/ x = u \/ x = v.
Proof.
  intros g u v e x.
  unfold vvalid, graph_instance, add_edge_graph; simpl.
  split.
  - intros [Hx | [Hx | Hx]]; subst; auto.
  - intros [Hx | [Hx | Hx]]; subst; auto.
Qed.

Lemma add_edge_graph_evalid_any :
  forall g u v e a,
    evalid (add_edge_graph g u v e) a <-> evalid g a \/ a = e.
Proof.
  intros g u v e a.
  unfold evalid, graph_instance, add_edge_graph; simpl.
  split.
  - intros [Ha | Ha]; [right; symmetry; exact Ha | left; exact Ha].
  - intros [Ha | Ha]; [right; exact Ha | left; symmetry; exact Ha].
Qed.

Lemma add_edge_graph_step_any :
  forall g u v e x y a,
    gvalid g ->
    ~ evalid g e ->
    step_aux (add_edge_graph g u v e) a x y <->
      step_aux g a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hne.
  unfold step_aux, graph_instance, graph_step,
    edge_endpoints_valid, edge_src, edge_dst, add_edge_graph.
  simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [left; reflexivity|].
        split.
        -- destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Heq | Hold] [_ Hxy]].
      { exfalso. apply Ha. symmetry; exact Heq. }
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [right; exact Hea|].
      split.
      * destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
        destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
Qed.

Lemma add_edge_graph_addEdge_any :
  forall g u v e,
    gvalid g ->
    ~ evalid g e ->
    addEdge g (add_edge_graph g u v e) u v e.
Proof.
  intros g u v e Hg Hne.
  constructor.
  - intros x. apply add_edge_graph_vvalid.
  - intros a. apply add_edge_graph_evalid_any.
  - intros x y a. apply add_edge_graph_step_any; auto.
Qed.

Lemma add_edge_graph_gvalid_new_vertex :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ vvalid g v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hvout.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold graph_step, edge_endpoints_valid, edge_src, edge_dst,
      add_edge_graph, graph_instance.
    simpl.
    destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
    split; [left; reflexivity |].
    split; [split; simpl; auto | left; split; reflexivity].
  - destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq].
    + subst a.
      exists u, v.
      unfold graph_step, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance.
      simpl.
      destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
      split; [left; reflexivity |].
      split; [split; simpl; auto | left; split; reflexivity].
    + specialize (Hg a Ha_old) as [x [y Hstep]].
      exists x, y.
      destruct Hstep as [_ [Hends Hxy]].
      unfold graph_step, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance in *.
      simpl in *.
      destruct (Z.eq_dec a e) as [Ha_eq' | _]; [contradiction |].
      split; [right; exact Ha_old |].
      destruct Hends as [Hsrc Hdst].
      split; [split; simpl; auto | exact Hxy].
Qed.

Lemma add_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    vvalid g v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hv.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
      edge_src, edge_dst, add_edge_graph.
    simpl.
    destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
    split; [left; reflexivity |].
    split; [split; simpl; auto | left; split; reflexivity].
  - destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq].
    + subst a.
      exists u, v.
      unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
        edge_src, edge_dst, add_edge_graph.
      simpl.
      destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
      split; [left; reflexivity |].
      split; [split; simpl; auto | left; split; reflexivity].
    + specialize (Hg a Ha_old) as [x [y Hstep]].
      exists x, y.
      destruct Hstep as [_ [Hends Hxy]].
      unfold step_aux, graph_instance, graph_step, edge_endpoints_valid,
        edge_src, edge_dst, add_edge_graph in *.
      simpl in *.
      destruct (Z.eq_dec a e) as [Ha_eq' | _]; [contradiction |].
      split; [right; exact Ha_old |].
      destruct Hends as [Hsrc Hdst].
      split; [split; simpl; auto | exact Hxy].
Qed.

Lemma remove_edge_graph_vvalid :
  forall g e x,
    vvalid (remove_edge_graph g e) x <-> vvalid g x.
Proof.
  intros g e x; reflexivity.
Qed.

Lemma remove_edge_graph_evalid :
  forall g e a,
    evalid (remove_edge_graph g e) a <-> evalid g a /\ a <> e.
Proof.
  intros g e a.
  unfold evalid, graph_instance, remove_edge_graph; simpl.
  split.
  - intros Hin.
    apply filter_In in Hin as [Hin Hfilter].
    destruct (Z.eq_dec a e) as [Ha | Ha]; [discriminate|].
    split; auto.
  - intros [Hin Hneq].
    apply filter_In.
    split; [exact Hin|].
    destruct (Z.eq_dec a e) as [Ha | Ha]; [contradiction|reflexivity].
Qed.

Lemma remove_edge_graph_step :
  forall g u v e x y a,
    gvalid g ->
    step_aux g e u v ->
    step_aux g a x y <->
      step_aux (remove_edge_graph g e) a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hstep.
  unfold step_aux, graph_instance, graph_step,
    edge_endpoints_valid, edge_src, edge_dst, remove_edge_graph.
  simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros Hcur.
      right; split; [reflexivity|].
      change (step_aux g e x y) in Hcur.
      pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hcur)
        as [[-> ->] | [-> ->]]; auto.
    + intros [Hremove | [_ Hxy]].
      * destruct Hremove as [Hin _].
        apply filter_In in Hin as [_ Hkeep].
        destruct (Z.eq_dec e e) as [_ | Hbad]; [discriminate | contradiction].
      * destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
        change (step_aux g e v u).
        apply step_sym; exact Hstep.
  - split.
    + intros [Hea [Hends Hxy]].
      left; split.
      * apply filter_In.
        split; [exact Hea |].
        destruct (Z.eq_dec a e) as [Heq | _]; [contradiction | reflexivity].
      * split; [exact Hends|exact Hxy].
    + intros [Hremove | [Heq _]]; [| contradiction].
      destruct Hremove as [Hin [Hends Hxy]].
      apply filter_In in Hin as [Hea _].
      split; [exact Hea | split; auto].
Qed.

Lemma remove_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    step_aux g e u v ->
    gvalid (remove_edge_graph g e).
Proof.
  intros g u v e Hg Hstep.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold remove_edge_graph in Ha; simpl in Ha.
  apply filter_In in Ha as [Ha Hkeep].
  destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq]; [discriminate|].
  destruct (Hg a Ha) as [x [y Hstep_a]].
  exists x, y.
  pose proof (proj1 (remove_edge_graph_step g u v e x y a Hg Hstep) Hstep_a)
    as [Hremove | [Ha_eq Hnew]].
  - exact Hremove.
  - contradiction.
Qed.

#[export] Instance addEdgeInSubgraph_instance :
  addEdgeInSubgraph G V E.
Proof.
  constructor.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hv Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid; auto.
    + split.
      * apply add_edge_graph_addEdge_any; auto.
      * constructor.
        -- intros z Hz.
           rewrite add_edge_graph_vvalid in Hz.
           destruct Hz as [Hz | [-> | ->]].
           ++ apply Hsub; exact Hz.
           ++ apply Hsub; exact Hu.
           ++ apply Hsub; exact Hv.
        -- intros x y a Ha.
           rewrite add_edge_graph_step_any in Ha by auto.
           destruct Ha as [Ha_old | [Ha_new Hxy]].
           ++ apply Hsub; exact Ha_old.
           ++ subst a.
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep |].
              apply step_sym; exact Hstep.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hvout Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid_new_vertex; auto.
    + split.
      * apply add_edge_graph_addEdge_any; auto.
      * constructor.
        -- intros z Hz.
           rewrite add_edge_graph_vvalid in Hz.
           destruct Hz as [Hz | [-> | ->]].
           ++ apply Hsub; exact Hz.
           ++ apply Hsub; exact Hu.
           ++ eapply step_vvalid2; eauto.
        -- intros x y a Ha.
           rewrite add_edge_graph_step_any in Ha by auto.
           destruct Ha as [Ha_old | [Ha_new Hxy]].
           ++ apply Hsub; exact Ha_old.
           ++ subst a.
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep |].
              apply step_sym; exact Hstep.
  - intros g h u v e Hg Hh Hsub Hu Hv He Hstep.
    exists (remove_edge_graph h e).
    split.
    + eapply remove_edge_graph_gvalid; eauto.
    + split.
      * constructor.
        -- intros z.
           rewrite remove_edge_graph_vvalid.
           split.
           ++ intros Hz; left; exact Hz.
           ++ intros [Hz | [-> | ->]]; auto.
        -- intros a.
           rewrite remove_edge_graph_evalid.
           split.
           ++ intros Ha.
              destruct (Z.eq_dec a e) as [-> | Hneq]; auto.
           ++ intros [[Ha _] | ->]; auto.
        -- intros x y a.
           apply remove_edge_graph_step; auto.
      * split.
        -- constructor.
           ++ intros z Hz.
              rewrite remove_edge_graph_vvalid in Hz.
              apply Hsub; exact Hz.
           ++ intros x y a Ha.
              apply Hsub.
              apply (proj2 (remove_edge_graph_step h u v e x y a Hh Hstep)).
              left; exact Ha.
        -- repeat split.
           ++ rewrite remove_edge_graph_vvalid; exact Hu.
           ++ rewrite remove_edge_graph_vvalid; exact Hv.
           ++ rewrite remove_edge_graph_evalid.
              intros [_ Hneq]; auto.
Qed.

#[export] Instance addEdgeGValid_instance :
  addEdgeGValid G V E.
Proof.
  constructor.
  intros g h u v e Hg Hadd.
  destruct Hadd as [_ Hadd_evalid Hadd_step].
  intros a Ha.
  apply Hadd_evalid in Ha as [Ha | ->].
  - destruct (Hg a Ha) as [x [y Hstep]].
    exists x, y.
    apply Hadd_step.
    left; exact Hstep.
  - exists u, v.
    apply Hadd_step.
    right; split; [reflexivity|auto].
Qed.

(** * Kruskal 抽象程序包装

    Kruskal 的抽象程序本身是 [whileP]，所以从任意中间状态继续执行时，
    仍然使用同一个 [Kruskal g]，不需要额外定义 [Kruskal_loop]。 *)

Definition graph_selectable_edge (g h : G) (e : E) : Prop :=
  evalid g e /\
  forall u v,
    step_aux g e u v ->
    ~ reachable h u v.

Definition forest_has_no_cycle (h : G) : Prop :=
  forall u,
    ~ exists p, is_simple_epath h u p u /\ p <> nil.

Definition forest_has_mst_extension (g h : G) : Prop :=
  exists y, is_mst g y /\ subgraph2 h y.

(** This is the cardinality/component law needed by the abstract while guard.
    It is stated for the multigraph model directly, without a [SimpleGraph]
    instance, so parallel input edges do not weaken the loop specification. *)
Definition kruskal_forest_progress_property (g : G) : Prop :=
  forall h,
    gvalid h ->
    forest_has_no_cycle h ->
    forest_has_mst_extension g h ->
    subgraph_vertex_eq h g ->
    ((exists e, graph_selectable_edge g h e) <->
     graph_edge_count h < graph_vertex_count g - 1).

Record KruskalEnv (g : G) : Prop := mkKruskalEnv {
  kruskal_graph_valid : gvalid g;
  kruskal_connected : connected g;
  kruskal_forest_progress : kruskal_forest_progress_property g;
}.

Definition return_is_mst (g rg : G) : Prop :=
  is_mst g rg.

Definition edge_arrays_ordered_by
    (m : Z)
    (orig_u orig_v orig_w : list Z)
    (edge_u edge_v edge_w edge_order : list Z) : Prop :=
  Zlength orig_u = m /\
  Zlength orig_v = m /\
  Zlength orig_w = m /\
  Zlength edge_u = m /\
  Zlength edge_v = m /\
  Zlength edge_w = m /\
  Zlength edge_order = m /\
  Permutation edge_order (Zrange 0 m) /\
  (forall i, 0 <= i < m ->
    let e := Znth i edge_order (-1) in
    0 <= e < m /\
    Znth i edge_u 0 = Znth e orig_u 0 /\
    Znth i edge_v 0 = Znth e orig_v 0 /\
    Znth i edge_w 0 = Znth e orig_w 0).

Definition edge_arrays_sorted_by_weight
    (edge_w edge_order : list Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < Zlength edge_order ->
    Znth i edge_w 0 <= Znth j edge_w 0.

Definition after_sorted_edge_of_input
    (m : Z)
    (orig_u orig_v orig_w : list Z)
    (edge_u edge_v edge_w edge_order : list Z) : Prop :=
  edge_arrays_ordered_by m orig_u orig_v orig_w edge_u edge_v edge_w edge_order /\
  edge_arrays_sorted_by_weight edge_w edge_order.

(** ** 边表 quicksort 规格辅助谓词 *)

Definition same_outside_edge_arrays_range
    (edge_u edge_v edge_w edge_order : list Z)
    (edge_u' edge_v' edge_w' edge_order' : list Z)
    (left right : Z) : Prop :=
  forall i,
    0 <= i ->
    (i < left \/ right < i) ->
    Znth i edge_u 0 = Znth i edge_u' 0 /\
    Znth i edge_v 0 = Znth i edge_v' 0 /\
    Znth i edge_w 0 = Znth i edge_w' 0 /\
    Znth i edge_order (-1) = Znth i edge_order' (-1).

Definition edge_arrays_partitioned_by_weight_at
    (edge_w : list Z) (left right pivot : Z) : Prop :=
  left <= pivot <= right /\
  (forall i,
    left <= i < pivot ->
    Znth i edge_w 0 < Znth pivot edge_w 0) /\
  (forall i,
    pivot < i <= right ->
    Znth pivot edge_w 0 <= Znth i edge_w 0).

Definition kruskal_result_graph_matches_array
    (ru rv rw : list Z) (g rg : G) : Prop :=
  0 <= Zlength (graph_vertices g) /\
  Zlength ru = Zlength (graph_vertices g) - 1 /\
  Zlength rv = Zlength (graph_vertices g) - 1 /\
  Zlength rw = Zlength (graph_vertices g) - 1 /\
  (forall i,
    In i (Zrange 0 (Zlength (graph_vertices g) - 1)) ->
    exists e,
      evalid rg e /\
      step_aux rg e (Znth i ru 0) (Znth i rv 0) /\
      weight g e = Some (Znth i rw 0)) /\
  (forall e,
    evalid rg e ->
    exists i,
      In i (Zrange 0 (Zlength (graph_vertices g) - 1)) /\
      step_aux rg e (Znth i ru 0) (Znth i rv 0) /\
      weight g e = Some (Znth i rw 0)).
