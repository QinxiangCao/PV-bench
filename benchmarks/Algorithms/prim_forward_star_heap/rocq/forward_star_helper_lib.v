Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
From GraphLib.examples Require Import prim.
From ListLib Require Import Base.Positional General.Length.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
From MonadLib.StateRelMonad Require Export StateRelBasic.
From MonadLib.StateRelMonad Require Import StateRelHoare FixpointLib safeexec_lib.
Require Algorithms.Prim.Prim.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.

(** * 具体图模型 *)

Definition V : Type := Z.
Definition E : Type := Z.
Definition DE : Type := Z.

Record G : Type := mkG {
  graph_from : E -> V;
  graph_to : E -> V;
  graph_weight : E -> Z;
  graph_vertices : list V;
  graph_edges : list E;
}.

(** ** C 数组规格使用的列表取值辅助函数 *)

(** ** 图的基本操作和良构条件 *)

Definition edge_src (g : G) (e : E) : V :=
  graph_from g e.

Definition edge_dst (g : G) (e : E) : V :=
  graph_to g e.

Definition graph_edge_count (g : G) : Z :=
  Zlength (graph_edges g).

Definition edge_endpoints_valid (g : G) (e : E) : Prop :=
  In (edge_src g e) (graph_vertices g) /\
  In (edge_dst g e) (graph_vertices g).

Definition edge_valid (g : G) (e : E) : Prop :=
  In e (graph_edges g).

Definition graph_step (g : G) (e : E) (u v : V) : Prop :=
  edge_valid g e /\
  edge_endpoints_valid g e /\
  ((u = edge_src g e /\ v = edge_dst g e) \/
   (u = edge_dst g e /\ v = edge_src g e)).

Definition graph_step_wf (g : G) : Prop :=
  forall e, edge_valid g e -> exists u v, graph_step g e u v.

Definition graph_wf : G -> Prop := graph_step_wf.

(** * GraphLib 图接口实例 *)

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := fun g v => In v (graph_vertices g);
  evalid := edge_valid;
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
  intros g e x1 y1 x2 y2 Hg H1 H2.
  destruct H1 as [_ [_ Hxy1]].
  destruct H2 as [_ [_ Hxy2]].
  destruct Hxy1 as [[-> ->] | [-> ->]];
    destruct Hxy2 as [[-> ->] | [-> ->]]; auto.
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := graph_vertices |}.
  intros g Hg v Hv; exact Hv.
Qed.

Definition valid_edges (g : G) : list E :=
  nodup Z.eq_dec (graph_edges g).

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := valid_edges |}.
  - intros g Hg.
    unfold valid_edges.
    apply NoDup_nodup.
  - intros g Hg e.
    unfold valid_edges, edge_valid.
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

(** * Prim 相关接口和包装 *)

Definition St : Type := @Prim.St G.

Definition empty_graph_of (g : G) (src : V) : G :=
  mkG (graph_from g) (graph_to g) (graph_weight g) (src :: nil) nil.

Lemma empty_graph_valid_of : forall g src, gvalid (empty_graph_of g src).
Proof.
  intros g src.
  unfold gvalid, gvalid_instance, graph_wf.
  intros e He.
  contradiction.
Qed.

#[export] Instance emptyGraph_instance (g : G) (src : V) :
  Prim.emptyGraph G V E src.
Proof.
  refine {| Prim.empty_graph := empty_graph_of g src |}.
  - apply empty_graph_valid_of.
  - intros v. simpl. split.
    + intros [Hv | []]; auto.
    + intros ->; auto.
  - intros e. simpl. unfold edge_valid. split; intros H.
    + destruct H.
    + contradiction.
Defined.

Definition initSt (g : G) (src : V) : St :=
  @Prim.initSt G V E graph_instance gvalid_instance src
    (emptyGraph_instance g src).

Definition initStPred (g : G) (src : V) : St -> Prop :=
  fun s => s = initSt g src.

Definition state_vertex_count (s : St) : Z :=
  vertex_num s.(Prim.graph_in_state).

Definition Prim2 (g : G) : program St unit :=
  @range_iter St unit
    0
    (Zlength (bijective_listV g) - 1)
    (fun _ _ =>
       @Prim.Prim_body G V E graph_instance g edge_weight_instance)
    tt.

Definition Prim2_loop (g : G) (i : Z) : program St unit :=
  @range_iter St unit
    i
    (Zlength (bijective_listV g) - 1)
    (fun _ _ =>
       @Prim.Prim_body G V E graph_instance g edge_weight_instance)
    tt.

Definition prim_state_is (s0 : St) : St -> Prop :=
  fun s => s = s0.

Definition prim_state_graph_matches (g:G) : St -> Prop :=
  fun s => s.(Prim.graph_in_state) = g.

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

Lemma add_edge_graph_evalid :
  forall g u v e a,
    vvalid g u ->
    vvalid g v ->
    ~ evalid g e ->
    evalid (add_edge_graph g u v e) a <-> evalid g a \/ a = e.
Proof.
  intros g u v e a Hu Hv Hne.
  unfold evalid, graph_instance, edge_valid, add_edge_graph; simpl.
  split.
  - intros [Ha | Ha]; [right; symmetry; exact Ha | left; exact Ha].
  - intros [Ha | Ha]; [right; exact Ha | left; symmetry; exact Ha].
Qed.

Lemma add_edge_graph_step :
  forall g u v e x y a,
    gvalid g ->
    vvalid g u ->
    vvalid g v ->
    ~ evalid g e ->
    step_aux (add_edge_graph g u v e) a x y <->
      step_aux g a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hu Hv Hne.
  unfold step_aux, graph_instance, graph_step.
  rewrite add_edge_graph_evalid by auto.
  unfold edge_src, edge_dst, add_edge_graph; simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [right; reflexivity|].
        split.
        -- unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph; simpl.
           destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Hold | Heq] [_ Hxy]]; [|contradiction].
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [left; exact Hea|].
      split.
      * unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph in *; simpl in *.
        destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
        destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
Qed.

Lemma add_edge_graph_evalid_any :
  forall g u v e a,
    evalid (add_edge_graph g u v e) a <-> evalid g a \/ a = e.
Proof.
  intros g u v e a.
  unfold evalid, graph_instance, edge_valid, add_edge_graph; simpl.
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
  unfold step_aux, graph_instance, graph_step.
  rewrite add_edge_graph_evalid_any.
  unfold edge_src, edge_dst, add_edge_graph; simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [right; reflexivity|].
        split.
        -- unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph; simpl.
           destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Hold | Heq] [_ Hxy]]; [|contradiction].
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [left; exact Hea|].
      split.
      * unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph in *; simpl in *.
        destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
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
  unfold gvalid, gvalid_instance, graph_wf, graph_step_wf in *.
  intros a Ha.
  unfold edge_valid, add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold graph_step, edge_valid, edge_endpoints_valid, edge_src, edge_dst,
      add_edge_graph, graph_instance.
    simpl.
    destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
    split; [left; reflexivity |].
    split; [split; simpl; auto | left; split; reflexivity].
  - destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq].
    + subst a.
      exists u, v.
      unfold graph_step, edge_valid, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance.
      simpl.
      destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
      split; [left; reflexivity |].
      split; [split; simpl; auto | left; split; reflexivity].
    + specialize (Hg a Ha_old) as [x [y Hstep]].
      exists x, y.
      destruct Hstep as [_ [Hends Hxy]].
      unfold graph_step, edge_valid, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance in *.
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
  unfold evalid, graph_instance, edge_valid, remove_edge_graph; simpl.
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
  unfold step_aux, graph_instance, graph_step.
  rewrite remove_edge_graph_evalid.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros Hcur.
      right; split; [reflexivity|].
      change (step_aux g e x y) in Hcur.
      pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hcur)
        as [[-> ->] | [-> ->]]; auto.
    + intros [[[ _ Hneq] _] | [_ Hxy]]; [contradiction|].
      destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
      change (step_aux g e v u).
      apply step_sym; exact Hstep.
  - split.
    + intros [Hea [Hends Hxy]].
      left; split; [split; auto|].
      split; [exact Hends|exact Hxy].
    + intros [[[Hea _] [Hends Hxy]] | [Heq _]]; [split; auto|contradiction].
Qed.

#[export] Instance addEdgeExist_instance :
  addEdgeExist G V E.
Proof.
  constructor.
  - intros g u v e Hg Hu Hv Hne.
    exists (add_edge_graph g u v e).
    split.
    + intros a Ha.
      rewrite add_edge_graph_evalid in Ha by auto.
      destruct Ha as [Ha | ->].
      * destruct (Hg a Ha) as [x [y Hstep]].
        exists x, y.
        rewrite add_edge_graph_step by auto.
        left; exact Hstep.
      * exists u, v.
        rewrite add_edge_graph_step by auto.
        right; split; [reflexivity|auto].
    + constructor.
      * intros x. apply add_edge_graph_vvalid.
      * intros a. apply add_edge_graph_evalid; auto.
      * intros x y a. apply add_edge_graph_step; auto.
  - intros g u v e Hg Hu Hv He Hstep.
    exists (remove_edge_graph g e).
    split.
    + intros a Ha.
      rewrite remove_edge_graph_evalid in Ha.
      destruct Ha as [Ha Hneq].
      destruct (Hg a Ha) as [x [y Hstep_a]].
      destruct (proj1 (remove_edge_graph_step g u v e x y a Hg Hstep) Hstep_a)
        as [Hremove | [Heq _]].
      * exists x, y; exact Hremove.
      * contradiction.
    + split.
      * constructor.
        -- intros x. rewrite remove_edge_graph_vvalid.
           split.
           ++ intros Hx; left; exact Hx.
           ++ intros [Hx | [Hx | Hx]].
              ** exact Hx.
              ** subst; exact Hu.
              ** subst; exact Hv.
        -- intros a. rewrite remove_edge_graph_evalid. split.
           ++ intros Ha; destruct (Z.eq_dec a e) as [-> | Hneq]; auto.
           ++ intros [[Ha _] | ->]; [exact Ha | exact He].
        -- intros x y a. apply remove_edge_graph_step; auto.
      * repeat split.
        -- rewrite remove_edge_graph_vvalid; exact Hu.
        -- rewrite remove_edge_graph_vvalid; exact Hv.
        -- rewrite remove_edge_graph_evalid. intros [_ Hneq]; auto.
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

Record PrimEnv (g : G) (src : V) : Prop := mkPrimEnv {
  prim_graph_valid : gvalid g;
  prim_src_valid : vvalid g src;
  prim_connected : connected g;
}.

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

(** * 由原图拆出的有向边数组 *)

Definition directed_array_graph_prefix
    (e_bound : E)
    (g : G)
    (from_new to_new wt_new : list DE) : Prop :=
  0 <= e_bound <= graph_edge_count g /\
  Zlength from_new = 2 * e_bound /\
  Zlength to_new = 2 * e_bound /\
  Zlength wt_new = 2 * e_bound /\
  forall e,
    0 <= e < e_bound ->
    Znth (2 * e) from_new 0 = graph_from g e /\
    Znth (2 * e) to_new 0 = graph_to g e /\
    Znth (2 * e) wt_new 0 = graph_weight g e /\
    Znth (2 * e + 1) from_new 0 = graph_to g e /\
    Znth (2 * e + 1) to_new 0 = graph_from g e /\
    Znth (2 * e + 1) wt_new 0 = graph_weight g e.

Definition directed_array_graph
    (g : G)
    (from_new to_new wt_new : list DE) : Prop :=
  directed_array_graph_prefix (graph_edge_count g) g from_new to_new wt_new.

(** * 基于有向边编号的 first/link 邻接表 *)

(** [is_link_chain link cur l] 表示从 cur 开始沿着 link 走，
    检查是否恰好走出有向边编号列表 l，并且最后在 -1 处结束。
    [is_first_link_chain] 则从 [Znth v first 0] 开始走这条链。 *)

Inductive is_link_chain (link : list DE) : DE -> list DE -> Prop :=
| is_link_chain_nil :
    is_link_chain link (-1) nil
| is_link_chain_cons :
    forall cur l,
      cur <> -1 ->                        
      is_link_chain link (Znth cur link 0) l ->
      is_link_chain link cur (cur :: l).

Definition is_first_link_chain
    (link first : list DE) (v : V) (l : list DE) : Prop :=
  is_link_chain link (Znth v first 0) l.

(**在已插入邻接表的有向边中，起点是v的所有有向边*)
Definition inserted_vertex_directed_edges
    (de_bound : DE) (from_new : list DE) (v : V) : list DE :=
  filter
    (fun de =>
      if Z.eq_dec (Znth de from_new 0) v then true else false)
    (Zrange 0 de_bound).

Definition vertex_directed_edges
    (g : G) (from_new : list DE) (v : V) : list DE :=
  inserted_vertex_directed_edges (2 * graph_edge_count g) from_new v.

(**已插入de_bound条有向边，检验first link的邻接表是否能表达此时所有点的出边*)
Definition first_link_matches_inserted_vertex_directed_edges
    (g : G) (de_bound : DE) (from_new : list DE) (first link : list DE) : Prop :=
  Zlength first = Zlength (graph_vertices g) /\
  Zlength link = 2 * graph_edge_count g /\
  0 <= de_bound <= Zlength link /\
  forall v,
    In v (graph_vertices g) ->
    exists cl : list DE,
      is_first_link_chain link first v cl /\
      Permutation cl (inserted_vertex_directed_edges de_bound from_new v).

Definition first_link_matches_vertex_directed_edges
    (g : G) (from_new : list DE) (first link : list DE) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    exists cl : list DE,
      is_first_link_chain link first v cl /\
      Permutation cl (vertex_directed_edges g from_new v).

Definition growing_subgraph_state (g: G) (s:St) : Prop :=
  gvalid s.(Prim.graph_in_state) /\
  connected s.(Prim.graph_in_state) /\
  subgraph2 s.(Prim.graph_in_state) g.

Definition visited_matches_state (g: G)(s: St) (visited : list Z) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    (Znth v visited 0 <> 0 <-> vvalid s.(Prim.graph_in_state) v).

    
(** edge_parent 中已经加入生长图的点对应合法的有向边编号。 *)
Definition parent_edges_range_state
    (g : G) (src : V) (s : St) (edge_parent : list DE) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    v <> src ->
    vvalid s.(Prim.graph_in_state) v ->
    0 <= Znth v edge_parent 0 < 2 * graph_edge_count g.

(** edge_parent 精确枚举当前生长图中的边。
    对当前生长图中的每条无向边 e，它必须来自某个非源、已加入顶点 v
    记录的有向父边 edge_parent[v]；反过来，每个这样的父边也必须在生长图中有效。 *)
Definition parent_edges_exact_state
    (g : G) (src : V) (s : St) (edge_parent : list DE) : Prop :=
  forall e,
    evalid s.(Prim.graph_in_state) e <->
    exists v,
      In v (graph_vertices g) /\
      v <> src /\
      vvalid s.(Prim.graph_in_state) v /\
      e = Znth v edge_parent 0 / 2.

(** edge_parent 是否真实描述当前生长图的父边集合。 *)
Definition parent_edges_match_state
    (g : G) (src : V) (s : St) (edge_parent : list DE) : Prop :=
  vvalid s.(Prim.graph_in_state) src /\
  parent_edges_range_state g src s edge_parent /\
  parent_edges_exact_state g src s edge_parent.

(** 判断是否是指向外部点v的割边 *)

Definition is_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  ~ vvalid s.(Prim.graph_in_state) v /\
  (edge_src g e = v \/ edge_dst g e = v) /\
  Prim.is_cut_edge g s e.

(**判断是否是指向外部点v的最小割边*)
Definition is_min_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => is_cut_edge_to_vertex g s v e)
    (weight g)
    e.

(** 判断点v目前是否已经有了加入生长子图的最小代价以及实现这个代价的边 *)
Definition vertex_has_parent_edge
    (g : G) (s : St) (lowcost:list Z) ( edge_parent : list DE) (inf : Z) (v : V) : Prop :=
  let de := Znth v edge_parent 0 in
  de <> -1 /\
  0 <= de < 2 * graph_edge_count g /\
  Znth v lowcost 0 < inf /\
  is_min_cut_edge_to_vertex g s v (de / 2) /\
  weight g (de / 2) = Some (Znth v lowcost 0).

(**判断点v是否是与生长子图相邻的侯选点*)
Definition candidate_vertex
    (g : G) (s : St) (lowcost:list Z) (edge_parent : list DE) (inf : Z) (v : V) : Prop :=
  In v (graph_vertices g) /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  vertex_has_parent_edge g s lowcost edge_parent inf v.

Definition candidate_vertex_exists_in_range
    (n : Z) (g : G) (s : St)
    (lowcost:list Z) (edge_parent : list DE) (inf : Z) : Prop :=
  exists v,
    In v (Zrange 0 n) /\
    candidate_vertex g s lowcost edge_parent inf v.

(*有可能扫描到第j个点还没有找到候选点，如果找到了候选点，要求其lowcost当前最小*)  
Definition min_vertex_in_range
    (g : G) (s : St)
    (j inf :Z) (minIndex :V) (lowcost:list Z) (edge_parent : list DE) : Prop :=
  (minIndex = -1 /\
   forall v,
     In v (Zrange 0 j) ->
     ~ candidate_vertex g s lowcost edge_parent inf v) \/
  (candidate_vertex g s lowcost edge_parent inf minIndex /\
   In minIndex (Zrange 0 j) /\
   min_object_of_subset Z_op_le
	     (fun v =>
	        In v (Zrange 0 j) /\
	         candidate_vertex g s lowcost edge_parent inf v)
		     (fun v => Some (Znth v lowcost 0))
		     minIndex).

     (*判断edge_parent【minIndex】储存的确实是当前生长子图s的所有割边里最小的*)
Definition selected_parent_edge_is_min_cut_edge
    (g : G) (s : St) (edge_parent : list DE) (minIndex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => Prim.is_cut_edge g s e)
    (weight g)
    (Znth minIndex edge_parent 0 / 2).

(*找出Prim.v里x <- get (fun s '(u, v) => vvalid s.(graph_in_state) u /\ ~ vvalid s.(graph_in_state) v /\ step_aux g e u v)要求的序对*)
Definition selected_parent_pair
    (g : G) (s : St)
    (from_new to_new edge_parent : list DE)
    (minIndex u v : V) : Prop :=
  let e := Znth minIndex edge_parent 0 / 2 in
  v = minIndex /\
  vvalid s.(Prim.graph_in_state) u /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  step_aux g e u v.

(*加边状态更新*)
Definition selected_parent_add_to_mst
    (g : G) (s s_next : St)
    (from_new to_new edge_parent : list DE)
    (minIndex : V) : Prop :=
  exists u v,
    selected_parent_pair g s from_new to_new edge_parent minIndex u v /\
    addEdge s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
      u v (Znth minIndex edge_parent 0 / 2).

(** * 扫描一条邻接表来更新 lowcost/parent *)

(** 这些谓词抽象 C 程序最后一层内循环：
    沿着被选中点的 [first/link] 链遍历所有出有向边，
    并用这些边更新 [lowcost] 和 [edge_parent]。 *)

(**判断沿邻接表扫描一条边后的更新操作是否正确，如果被扫描边确实是该边终点加入生长子图s割边且圈中比lowcost记录的小就更新，否则都不更新，*)
Definition scan_one_directed_edge_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z)
    (lowcost_in:list Z) (edge_parent_in : list DE)
    (de : DE)
    (lowcost_out:list Z) (edge_parent_out : list DE) : Prop :=
  let v := Znth de to_new 0 in
  let w := Znth de wt_new 0 in
  (is_cut_edge_to_vertex g s_next v (de / 2) /\
   w < Znth v lowcost_in 0 /\
   lowcost_out = replace_Znth v w lowcost_in /\
   edge_parent_out = replace_Znth v de edge_parent_in) \/
  ((~ is_cut_edge_to_vertex g s_next v (de / 2) \/
    Znth v lowcost_in 0 <= w) /\
   lowcost_out = lowcost_in /\
   edge_parent_out = edge_parent_in).

(** 扫描一串有向边后的数组更新关系。
    参数顺序：
    [scanned_edges] 是已经扫描的有向边列表；
    [lowcost_before] / [edge_parent_before] 是扫描前的数组抽象值；
    [lowcost_after] / [edge_parent_after] 是扫描完这些边后的数组抽象值。
    递归扫描一条邻接表 *)
Inductive scan_directed_edges_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z) :
    list DE -> list Z -> list DE -> list Z -> list DE -> Prop :=
| scan_directed_edges_update_nil :
    forall lowcost edge_parent,
      scan_directed_edges_update
        g s_next to_new wt_new nil
        lowcost edge_parent lowcost edge_parent
| scan_directed_edges_update_cons :
    forall de rest
           lowcost0 edge_parent0
           lowcost1 edge_parent1
           lowcost2 edge_parent2,
      scan_one_directed_edge_update
        g s_next to_new wt_new
        lowcost0 edge_parent0 de lowcost1 edge_parent1 ->
      scan_directed_edges_update
        g s_next to_new wt_new rest
        lowcost1 edge_parent1 lowcost2 edge_parent2 ->
      scan_directed_edges_update
        g s_next to_new wt_new (de :: rest)
        lowcost0 edge_parent0 lowcost2 edge_parent2.

Definition scan_minIndex_adjacency_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (lowcost_after : list Z) (edge_parent_after : list DE) : Prop :=
  exists scanned_edges : list DE,
    is_first_link_chain link first minIndex scanned_edges /\
    Permutation scanned_edges (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after.

Definition scan_minIndex_adjacency_prefix_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V) (current_e : DE)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (lowcost_current : list Z) (edge_parent_current : list DE) : Prop :=
  exists scanned_edges remaining_edges : list DE,
    is_first_link_chain link first minIndex (scanned_edges ++ remaining_edges) /\
    is_link_chain link current_e remaining_edges /\
    Permutation (scanned_edges ++ remaining_edges)
      (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before
      lowcost_current edge_parent_current.

(** lowcost和edge_parent是否正确描述当前状态 *)

Definition lowcost_parent_match
    (g : G) (s : St)
    (lowcost:list Z) (edge_parent : list DE)
    (inf : Z) : Prop :=
  (forall v,
    In v (graph_vertices g) ->
    0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
	    In v (graph_vertices g) ->
	    ~ vvalid s.(Prim.graph_in_state) v ->
	    ((exists de,
		        Znth v edge_parent 0 = de /\
	        de <> -1 /\
	        0 <= de < 2 * graph_edge_count g /\
			        Znth v lowcost 0 < inf /\
	        is_min_cut_edge_to_vertex g s v (de / 2) /\
		        weight g (de / 2) = Some (Znth v lowcost 0)) \/
		     ((forall e, ~ is_cut_edge_to_vertex g s v e) /\
			      Znth v edge_parent 0 = -1 /\
			      Znth v lowcost 0 = inf)).

(** 参数化版本：把“点 v 当前可选的入树边集合”抽成 [edge_for_vertex]。
    后面扫描邻接表时会先维护这个泛化版本，最后再实例化回
    [is_cut_edge_to_vertex g s v]。 *)
Definition lowcost_parent_match_by
    (g : G)
    (eligible_vertex : V -> Prop)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost:list Z) (edge_parent : list DE)
    (inf : Z) : Prop :=
  (forall v,
    In v (graph_vertices g) ->
    0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
    In v (graph_vertices g) ->
    eligible_vertex v ->
    ((exists de,
        Znth v edge_parent 0 = de /\
        de <> -1 /\
        0 <= de < 2 * graph_edge_count g /\
        Znth v lowcost 0 < inf /\
        min_object_of_subset Z_op_le
          (edge_for_vertex v)
          (weight g)
          (de / 2) /\
        weight g (de / 2) = Some (Znth v lowcost 0)) \/
     ((forall e, ~ edge_for_vertex v e) /\
      Znth v edge_parent 0 = -1 /\
      Znth v lowcost 0 = inf)).

Definition add_scanned_edge_for_vertex
    (g : G) (s_next : St) (to_new : list DE)
    (edge_for_vertex : V -> E -> Prop) (de : DE)
    (v : V) (e : E) : Prop :=
  edge_for_vertex v e \/
  (v = Znth de to_new 0 /\
   e = de / 2 /\
   is_cut_edge_to_vertex g s_next v e).

Fixpoint add_scanned_edges_for_vertex
    (g : G) (s_next : St) (to_new : list DE)
    (edge_for_vertex : V -> E -> Prop) (scanned_edges : list DE)
    : V -> E -> Prop :=
  match scanned_edges with
  | nil => edge_for_vertex
  | de :: rest =>
      add_scanned_edges_for_vertex
        g s_next to_new
        (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
        rest
  end.

Definition add_vertex_directed_edges_for_vertex
    (g : G) (s_next : St)
    (from_new to_new : list DE) (minIndex : V)
    (edge_for_vertex : V -> E -> Prop)
    (v : V) (e : E) : Prop :=
  edge_for_vertex v e \/
  exists de,
    In de (vertex_directed_edges g from_new minIndex) /\
    v = Znth de to_new 0 /\
    e = de / 2 /\
    is_cut_edge_to_vertex g s_next v e.

Definition selected_state_after_add
    (g : G) (src : V) (i n : Z)
    (s_before s_after : St)
    (from_new to_new edge_parent lowcost visited : list Z)
    (minIndex : V) : Prop :=
  (i = 0 /\
   minIndex = src /\
   initStPred g src s_after /\
   lowcost = replace_Znth src 0 (repeat 1000000000 (Z.to_nat n)) /\
   edge_parent = repeat (-1) (Z.to_nat n) /\
   visited = repeat 0 (Z.to_nat n) /\
   visited_matches_state g s_after (replace_Znth minIndex 1 visited)) \/
  (1 <= i < n /\
   growing_subgraph_state g s_before /\
   visited_matches_state g s_before visited /\
   lowcost_parent_match g s_before lowcost edge_parent 1000000000 /\
   selected_parent_edge_is_min_cut_edge g s_before edge_parent minIndex /\
   exists u v,
     selected_parent_pair g s_before from_new to_new edge_parent minIndex u v /\
     selected_parent_add_to_mst
       g s_before s_after from_new to_new edge_parent minIndex /\
     visited_matches_state g s_after (replace_Znth minIndex 1 visited)).

      

Definition prim_result_graph_matches_array
    (n: Z) (rf rt rw: list Z) (g rg : G) : Prop :=
  0 <= n /\
  (forall v, In v (Zrange 0 n) -> vvalid rg v) /\
  Zlength rf = n - 1 /\
  Zlength rt = n - 1 /\
  Zlength rw = n - 1 /\
  (forall i, In i (Zrange 0 (n - 1)) ->
    exists e,
      evalid rg e /\
      step_aux rg e (Znth i rf 0) (Znth i rt 0) /\
      weight g e = Some (Znth i rw 0)) /\
  (forall e,
    evalid rg e ->
    exists i,
      In i (Zrange 0 (n - 1)) /\
      step_aux rg e (Znth i rf 0) (Znth i rt 0) /\
      weight g e = Some (Znth i rw 0)).

(** 返回数组前缀的循环不变量。
    中间阶段不只记录长度，还记录第 k 个输出槽位对应点 k+1 的 parent 边。
    由于输出循环按 i = 1,2,... 扫描，前缀 idx 正好对应顶点 1..idx。 *)
Definition prim_result_graph_matches_array_prefix
    (n idx : Z) (rf rt rw : list Z) (g rg : G)
    (edge_parent from_new to_new wt_new : list Z) : Prop :=
  0 <= idx <= n - 1 /\
  Zlength rf = idx /\
  Zlength rt = idx /\
  Zlength rw = idx /\
  (forall k,
    In k (Zrange 0 idx) ->
    let de := Znth (k + 1) edge_parent 0 in
    let e := de / 2 in
    evalid rg e /\
    step_aux rg e (Znth k rf 0) (Znth k rt 0) /\
    weight g e = Some (Znth k rw 0) /\
    Znth k rf 0 = Znth de from_new 0 /\
    Znth k rt 0 = Znth de to_new 0 /\
    Znth k rw 0 = Znth de wt_new 0).

