Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import IntLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
From GraphLib.examples Require Import prim.
From ListLib Require Import Base.Positional.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
From MonadLib.StateRelMonad Require Export StateRelBasic.
From MonadLib.StateRelMonad Require Import StateRelHoare FixpointLib safeexec_lib.
Require Algorithms.Prim.Prim.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Import ListNotations.
Import MonadNotation.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Definition V : Type := Z.

Definition E : Type := (V * V)%type.

Definition E_eq_dec : forall e1 e2 : E, {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality; apply Z.eq_dec.
Defined.

Definition edge_connects (e : E) (u v : V) : Prop :=
  (fst e = u /\ snd e = v) \/
  (fst e = v /\ snd e = u).

(** [undirected_edge u v] 是由两个端点确定的无向边表示。
    为了让[(u,v)]和[(v,u)]表示同一条边，这里总是把较小端点放在前面。 *)
Definition undirected_edge (u v : V) : E :=
  if Z.leb u v then (u, v) else (v, u).

Record G : Type := mkG {
  graph_weight : E -> Z;
  graph_vertices : list V;
  graph_edges : list E;
}.

Definition default_edge : E := (-1, -1).

Definition default_edge_list (n : Z) : list E :=
  repeat default_edge (Z.to_nat n).

Definition edge_src (g : G) (e : E) : V :=
  fst e.

Definition edge_dst (g : G) (e : E) : V :=
  snd e.

Definition edge_endpoints_valid (g : G) (e : E) : Prop :=
  In (edge_src g e) (graph_vertices g) /\
  In (edge_dst g e) (graph_vertices g).

(** * GraphLib 图接口
 *)

Definition graph_step (g : G) (e : E) (x y : V) : Prop :=
  In e (graph_edges g) /\
  edge_endpoints_valid g e /\
  ((x = edge_src g e /\ y = edge_dst g e) \/
   (x = edge_dst g e /\ y = edge_src g e)).

Definition graph_wf (g : G) : Prop :=
  forall e, In e (graph_edges g) -> exists u v, graph_step g e u v.

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
    destruct Hstep as [_ [[Hu Hv] Hxy]].
    destruct Hxy as [[-> _] | [-> _]]; auto.
  - intros g e x y Hstep.
    destruct Hstep as [_ [[Hu Hv] Hxy]].
    destruct Hxy as [[_ ->] | [_ ->]]; auto.
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
  destruct Hstep as [He [[Hu Hv] Hxy]].
  repeat split; auto.
  destruct Hxy as [[-> ->] | [-> ->]]; auto.
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
  nodup E_eq_dec (graph_edges g).

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := valid_edges |}.
  - intros g Hg.
    unfold valid_edges.
    apply NoDup_nodup.
  - intros g _ e.
    unfold valid_edges.
    rewrite nodup_In.
    split; auto.
Qed.
#[export] Instance edge_weight_instance : EdgeWeight G E := {|
  weight := fun g e => Some (graph_weight g e);
|}.

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

(** * Prim 状态接口

    
 *)

Definition St : Type := @Prim.St G.

Definition empty_graph_of (g : G) (src : V) : G :=
  mkG (graph_weight g) (src :: nil) nil.

Lemma empty_graph_valid_of :
  forall g src, gvalid (empty_graph_of g src).
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
  - intros e. simpl. split; intros H.
    + destruct H.
    + contradiction.
Defined.

Definition initSt (g : G) (src : V) : St :=
  @Prim.initSt G V E graph_instance gvalid_instance src
    (emptyGraph_instance g src).

Definition initStPred (g : G) (src : V) : St -> Prop :=
  fun s => s = initSt g src.

Record PrimEnv (g : G) (src : V) : Prop := mkPrimEnv {
  prim_graph_valid : gvalid g;
  prim_src_valid : vvalid g src;
  prim_connected : connected g;
}.

Definition state_vertex_count (s : St) : Z :=
  vertex_num s.(Prim.graph_in_state).

Definition prim_state_is (s0 : St) : St -> Prop :=
  fun s => s = s0.

Definition prim_state_graph_matches (g : G) : St -> Prop :=
  fun s => s.(Prim.graph_in_state) = g.

Definition return_is_mst (g rg : G) : Prop :=
  is_mst g rg.

Definition growing_subgraph_state (g : G) (s : St) : Prop :=
  gvalid s.(Prim.graph_in_state) /\
  connected s.(Prim.graph_in_state) /\
  subgraph2 s.(Prim.graph_in_state) g /\
  (forall e, graph_weight s.(Prim.graph_in_state) e = graph_weight g e).

Definition visited_matches_state (g : G) (s : St) (visited : list Z) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    (Znth v visited 0 <> 0 <-> vvalid s.(Prim.graph_in_state) v).

(** ** ghost语义里维护一个叫edge_parent的list E 

    邻接矩阵版 C 程序不要求维护 edge_parent ；但是证明里仍维护一个 ghost的
    edge_parent来说明：
    - 每个已经加入生长图、且不是源点的顶点，都有一条合法 parent 边；
    - 当前生长图里的边，正好就是这些 parent 边。
    方便e <- get_min_cut_edge is_cut_edge这步。
 *)
Definition selected_edges_range_state
    (g : G) (src : V) (s : St) (edge_parent : list E) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    v <> src ->
    vvalid s.(Prim.graph_in_state) v ->
    In (Znth v edge_parent default_edge) (graph_edges g).

Definition selected_edges_exact_state
    (g : G) (src : V) (s : St) (edge_parent : list E) : Prop :=
  forall e,
    evalid s.(Prim.graph_in_state) e <->
    exists v,
      In v (graph_vertices g) /\
      v <> src /\
      vvalid s.(Prim.graph_in_state) v /\
      e = Znth v edge_parent default_edge.

Definition selected_edges_match_state
    (g : G) (src : V) (s : St) (edge_parent : list E) : Prop :=
  vvalid s.(Prim.graph_in_state) src /\
  selected_edges_range_state g src s edge_parent /\
  selected_edges_exact_state g src s edge_parent.

(** ** C层父点数组和ghost父边列表的桥接

    返回MST邻接矩阵的C程序会真实维护一个[vertex_parent]数组：
    [vertex_parent[v] = p]表示点[v]通过父点[p]连入MST。

    但抽象Prim证明仍沿用ghost的[edge_parent : list E]：
    [edge_parent[v]]表示点[v]连入MST所用的规范无向边。
/
 *)
Definition vertex_parent_matches_edge_parent
    (g : G) (src : V) (vertex_parent : list Z) (edge_parent : list E) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    0 <= v < Zlength vertex_parent /\
    0 <= v < Zlength edge_parent /\
    let p := Znth v vertex_parent (-1) in
    let e := Znth v edge_parent default_edge in
    (v = src -> p = -1 /\ e = default_edge) /\
    ((p = -1 /\ e = default_edge) \/
     (p <> -1 /\
      In p (graph_vertices g) /\
      p <> v /\
      e = undirected_edge p v /\
      graph_step g e p v)).

(** ** 加边操作

    [E] 是点对，所以边的端点由边本身决定。加边时不再“修改边编号
    的解释”，只是把这条边加入边集，并把端点加入点集。
 *)

Definition add_edge_graph (g : G) (u v : V) (e : E) : G :=
  mkG
    (graph_weight g)
    (u :: v :: graph_vertices g)
    (e :: graph_edges g).

Definition remove_edge_graph (g : G) (e : E) : G :=
  mkG
    (graph_weight g)
    (graph_vertices g)
    (filter (fun a => if E_eq_dec a e then false else true) (graph_edges g)).

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

Lemma add_edge_graph_step :
  forall g u v e x y a,
    gvalid g ->
    vvalid g u ->
    ~ evalid g e ->
    edge_connects e u v ->
    step_aux (add_edge_graph g u v e) a x y <->
      step_aux g a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hu Hne Hconn.
  unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
  split.
  - intros [[Ha | Ha] [Hends Hxy]].
    + subst a.
      right; split; [reflexivity|].
      unfold edge_connects in Hconn.
      destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
        destruct Hxy as [[Hx Hy] | [Hx Hy]];
        subst; auto.
    + left.
      destruct (Hg a Ha) as [p [q [_ [Hends_old _]]]].
      split; [exact Ha|split; [exact Hends_old|exact Hxy]].
  - intros [Hold | [Ha Hxy]].
    + destruct Hold as [Ha [Hends Hxy]].
      split; [right; exact Ha|].
      split.
      * destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
    + subst a.
      split; [left; reflexivity|].
      split.
      * unfold edge_connects in Hconn.
        destruct Hconn as [[<- <-] | [<- <-]];
          split; simpl; auto.
      * unfold edge_connects in Hconn.
        destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
          destruct Hxy as [[-> ->] | [-> ->]];
          subst; auto.
Qed.

Lemma add_edge_graph_addEdge :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ evalid g e ->
    edge_connects e u v ->
    addEdge g (add_edge_graph g u v e) u v e.
Proof.
  intros g u v e Hg Hu Hne Hconn.
  constructor.
  - intros x. apply add_edge_graph_vvalid.
  - intros a. apply add_edge_graph_evalid_any.
  - intros x y a. apply add_edge_graph_step; auto.
Qed.

Lemma graph_step_edge_connects :
  forall g e u v,
    step_aux g e u v ->
    edge_connects e u v.
Proof.
  intros g e u v Hstep.
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [_ [_ Huv]].
  unfold edge_connects, edge_src, edge_dst in *.
  destruct Huv as [[Hu Hv] | [Hu Hv]].
  - left; split; symmetry; assumption.
  - right; split; symmetry; assumption.
Qed.

Lemma add_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    edge_connects e u v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hconn.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
    split; [left; reflexivity|].
    split.
    + unfold edge_endpoints_valid, edge_src, edge_dst.
      unfold edge_connects in Hconn.
      destruct Hconn as [[<- <-] | [<- <-]]; simpl; split; auto.
    + unfold edge_connects in Hconn.
      destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
        subst; simpl; auto.
  - destruct (Hg a Ha_old) as [x [y Hstep]].
    exists x, y.
    destruct Hstep as [_ [Hends Hxy]].
    unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
    split; [right; exact Ha_old|].
    split.
    + destruct Hends as [Hsrc Hdst]; split; simpl; auto.
    + exact Hxy.
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
    destruct (E_eq_dec a e) as [Ha | Ha]; [discriminate |].
    split; auto.
  - intros [Hin Hneq].
    apply filter_In.
    split; [exact Hin |].
    destruct (E_eq_dec a e) as [Ha | Ha]; [contradiction | reflexivity].
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
  destruct (E_eq_dec a e) as [Ha | Ha].
  - subst a.
    unfold step_aux, graph_instance, graph_step.
    split.
    + intros Hcur.
      right; split; [reflexivity |].
      pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hcur)
        as [[-> ->] | [-> ->]]; auto.
    + intros [Hremove | [_ Hxy]].
      * destruct Hremove as [Hin _].
        unfold remove_edge_graph in Hin; simpl in Hin.
        apply filter_In in Hin as [_ Hfilter].
        destruct (E_eq_dec e e) as [_ | Hbad];
          [discriminate | exfalso; apply Hbad; reflexivity].
      * destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep |].
        change (step_aux g e v u).
        apply step_sym; exact Hstep.
  - split.
    + intros Hcur.
      destruct Hcur as [Hea [Hends Hxy]].
      left.
      unfold step_aux, graph_instance, graph_step, remove_edge_graph.
      simpl.
      split.
      * apply filter_In.
        split; [exact Hea |].
        destruct (E_eq_dec a e) as [Heq | _]; [contradiction | reflexivity].
      * split; [exact Hends | exact Hxy].
    + intros [Hremove | [Heq _]].
      * unfold step_aux, graph_instance, graph_step, remove_edge_graph in Hremove.
        simpl in Hremove.
        destruct Hremove as [Hin [Hends Hxy]].
        apply filter_In in Hin as [Hea _].
        unfold step_aux, graph_instance, graph_step.
        split; [exact Hea | split; auto].
      * contradiction.
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
  destruct (E_eq_dec a e) as [Ha_eq | Ha_neq]; [discriminate|].
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
    assert (Hconn : edge_connects e u v)
      by (apply graph_step_edge_connects with (g := g); exact Hstep).
    split.
    + apply add_edge_graph_gvalid; auto.
    + split.
      * apply add_edge_graph_addEdge; auto.
      * constructor.
        -- intros z Hz.
        rewrite add_edge_graph_vvalid in Hz.
        destruct Hz as [Hz | [-> | ->]].
        ++ apply Hsub; exact Hz.
        ++ apply Hsub; exact Hu.
        ++ apply Hsub; exact Hv.
        -- intros x y a Ha.
        rewrite add_edge_graph_step in Ha by auto.
        destruct Ha as [Ha_old | [Ha_new Hxy]].
        ++ apply Hsub; exact Ha_old.
        ++ subst a.
           destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
           apply step_sym; exact Hstep.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hvout Hne.
    exists (add_edge_graph s u v e).
    assert (Hconn : edge_connects e u v)
      by (apply graph_step_edge_connects with (g := g); exact Hstep).
    split.
    + apply add_edge_graph_gvalid; auto.
    + split.
      * apply add_edge_graph_addEdge; auto.
      * constructor.
        -- intros z Hz.
        rewrite add_edge_graph_vvalid in Hz.
        destruct Hz as [Hz | [-> | ->]].
        ++ apply Hsub; exact Hz.
        ++ apply Hsub; exact Hu.
        ++ eapply step_vvalid2; eauto.
        -- intros x y a Ha.
        rewrite add_edge_graph_step in Ha by auto.
        destruct Ha as [Ha_old | [Ha_new Hxy]].
        ++ apply Hsub; exact Ha_old.
        ++ subst a.
           destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
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
           destruct (E_eq_dec a e) as [-> | Hneq]; auto.
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
    right; split; [reflexivity | auto].
Qed.

Definition Prim2 (g : G) : program St unit :=
  @Prim.Prim2 G V E graph_instance gvalid_instance finite_instance
    g edge_weight_instance.

Definition Prim2_loop (g : G) (i : Z) : program St unit :=
  @range_iter St unit
    i
    (Zlength (bijective_listV g) - 1)
    (fun _ _ =>
       @Prim.Prim_body G V E graph_instance g edge_weight_instance)
    tt.

(** ** 邻接矩阵数组的下标语义

    C 侧采用 [int** graph]，规格侧用 [list (list Z)] 表示矩阵。
    因此抽象读取就是先取第 [u] 行，再取第 [v] 列。
 *)

Definition matrix_index_valid (n u v : Z) : Prop :=
  0 <= u < n /\ 0 <= v < n.

Definition matrix_entry (matrix : list (list Z)) (u v : V) : Z :=
  Znth v (Znth u matrix nil) 0.

Definition adjacency_matrix_shape (n : Z) (matrix : list (list Z)) : Prop :=
  Zlength matrix = n /\
  forall u, 0 <= u < n -> Zlength (Znth u matrix nil) = n.

Definition adjacency_matrix_model (n : Z) (matrix : list (list Z)) (g : G) (inf : Z) : Prop :=
  adjacency_matrix_shape n matrix /\
  (forall v, In v (graph_vertices g) <-> In v (Zrange 0 n)) /\
	  (forall u v,
	     0 <= u < n ->
	     0 <= v < n ->
	     matrix_entry matrix u v = inf \/
	     0 <= matrix_entry matrix u v < inf) /\
  graph_wf g /\
  (forall e,
     In e (graph_edges g) ->
     matrix_index_valid n (edge_src g e) (edge_dst g e) /\
     graph_weight g e = matrix_entry matrix (edge_src g e) (edge_dst g e) /\
     graph_weight g e = matrix_entry matrix (edge_dst g e) (edge_src g e) /\
     graph_weight g e <> inf) /\
  (forall u v,
     0 <= u < n ->
     0 <= v < n ->
     matrix_entry matrix u v <> inf ->
	     In (undirected_edge u v) (graph_edges g) /\
	     graph_step g (undirected_edge u v) u v /\
	     graph_weight g (undirected_edge u v) = matrix_entry matrix u v).

Definition prim_adjacency_matrix_graph_model
    (n : Z) (g : G) (inf : Z) (matrix : list (list Z)) : Prop :=
  adjacency_matrix_model n matrix g inf.

(** 最终返回值与结果图的关系。

    当前邻接矩阵版 C 程序返回的是 MST 的总权重，
    因此这里把返回整数 [ret] 解释为结果图 [rg] 中所有合法边权重之和。
 *)
Definition graph_total_weight (g : G) : Z :=
  fold_right Z.add 0 (map (graph_weight g) (valid_edges g)).

Definition prim_result_weight (rg : G) (ret : Z) : Prop :=
  ret = graph_total_weight rg.

Definition inf_matrix (rows cols inf : Z) : list (list Z) :=
  repeat (repeat_Z inf cols) (Z.to_nat rows).

Definition set_matrix_entry
    (matrix : list (list Z)) (u v value : Z) : list (list Z) :=
  replace_Znth u
    (replace_Znth v value (Znth u matrix nil))
    matrix.

Definition set_undirected_matrix_entry
    (matrix : list (list Z)) (u v value : Z) : list (list Z) :=
  set_matrix_entry (set_matrix_entry matrix u v value) v u value.

Definition processed_parent_edge_cell
    (g : G) (vertex_parent : list Z) (edge_parent : list E)
    (i u v w : Z) : Prop :=
  exists child parent e,
    In child (Zrange 0 i) /\
    In child (graph_vertices g) /\
    parent = Znth child vertex_parent (-1) /\
    parent <> -1 /\
    e = Znth child edge_parent default_edge /\
    e = undirected_edge parent child /\
    undirected_edge u v = e /\
    graph_step g e parent child /\
    graph_weight g e = w.

(** 构造返回矩阵时的前缀规格。

    [i]表示已经处理了顶点编号区间[0, i)。
    对任意矩阵格子[(u,v)]：
    - 如果它对应某个已处理点[child]的父边，则该格子必须等于这条父边权重；
    - 如果它不对应任何已处理父边，则该格子必须仍然是[inf]。

    这个谓词用于后处理循环；它需要[input_matrix]，因为C代码实际从
    [graph[p][v]]读取权重再写入[result_matrix]。
 *)
Definition result_matrix_parent_prefix
    (g : G) (src : V) (input_matrix result_matrix : list (list Z))
    (vertex_parent : list Z) (edge_parent : list E)
    (inf i : Z) : Prop :=
  adjacency_matrix_shape (Zlength input_matrix) result_matrix /\
  vertex_parent_matches_edge_parent g src vertex_parent edge_parent /\
  forall u v,
    In u (graph_vertices g) ->
    In v (graph_vertices g) ->
    (exists w,
       processed_parent_edge_cell g vertex_parent edge_parent i u v w /\
       matrix_entry result_matrix u v = w /\
       matrix_entry input_matrix u v = w) \/
    ((forall w,
        ~ processed_parent_edge_cell g vertex_parent edge_parent i u v w) /\
       matrix_entry result_matrix u v = inf).

(** 返回二维数组版本的结果规格。

    [rg]是不是MST由[safeExec ... Prim2 ...]和Prim正确性负责；
    这里直接要求返回矩阵[result_matrix]就是[rg]的邻接矩阵表示。
 *)
Definition prim_result_matrix_matches
    (result_matrix : list (list Z)) (rg : G) (inf : Z) : Prop :=
  adjacency_matrix_model (vertex_num rg) result_matrix rg inf.

Definition prim_input_weight_bound (n inf : Z) : Prop :=
  0 <= inf /\ n * inf <= INT64_MAX.

Definition prim_result_weight_in_int64_range (rg : G) : Prop :=
  INT64_MIN <= graph_total_weight rg /\
  graph_total_weight rg <= INT64_MAX.

Definition lowcost_prefix_sum (i : Z) (lowcost : list Z) : Z :=
  fold_right Z.add 0 (map (fun v => Znth v lowcost 0) (Zrange 0 i)).

Definition lowcost_vertex_sum (vertices : list V) (lowcost : list Z) : Z :=
  fold_right Z.add 0 (map (fun v => Znth v lowcost 0) vertices).

Definition lowcost_state_sum (s : St) (lowcost : list Z) : Z :=
  lowcost_vertex_sum
    (bijective_listV s.(Prim.graph_in_state))
    lowcost.

Definition lowcost_sum_matches_state (s : St) (lowcost : list Z) : Prop :=
  lowcost_state_sum s lowcost =
  graph_total_weight s.(Prim.graph_in_state) /\
  forall i,
    0 <= i < Zlength lowcost ->
    INT64_MIN <= lowcost_prefix_sum i lowcost + Znth i lowcost 0 /\
    lowcost_prefix_sum i lowcost + Znth i lowcost 0 <= INT64_MAX.

Definition lowcost_values_in_range (inf : Z) (lowcost : list Z) : Prop :=
  forall i,
    0 <= i < Zlength lowcost ->
    0 <= Znth i lowcost 0 <= inf.

(** ** lowcost 和 ghost edge_parent 与当前 Prim 状态的关系

    邻接矩阵 C 程序只真实保存 [lowcost]。这里额外维护一个 ghost
    [edge_parent] 列表：对尚未加入生长子图的点 [v]，
    [edge_parent[v]] 记录实现 [lowcost[v]] 的那条规范无向边。
 *)

Definition is_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  ~ vvalid s.(Prim.graph_in_state) v /\
  (edge_src g e = v \/ edge_dst g e = v) /\
  Prim.is_cut_edge g s e.

Definition is_min_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => is_cut_edge_to_vertex g s v e)
    (weight g)
    e.

Definition vertex_has_parent_edge
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) (v : V) : Prop :=
  let e := Znth v edge_parent default_edge in
  In e (graph_edges g) /\
  Znth v lowcost 0 < inf /\
  is_min_cut_edge_to_vertex g s v e /\
  weight g e = Some (Znth v lowcost 0).

Definition lowcost_parent_match
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) : Prop :=
  (forall v,
     In v (graph_vertices g) ->
     0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
    In v (graph_vertices g) ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    (vertex_has_parent_edge g s lowcost edge_parent inf v \/
		     ((forall e, ~ is_cut_edge_to_vertex g s v e) /\
		      Znth v lowcost 0 = inf)).

Definition vertex_has_parent_edge_by
    (g : G) (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list E) (inf : Z) (v : V) : Prop :=
  let e := Znth v edge_parent default_edge in
  In e (graph_edges g) /\
  Znth v lowcost 0 < inf /\
  min_object_of_subset Z_op_le
    (edge_for_vertex v)
    (weight g)
    e /\
  weight g e = Some (Znth v lowcost 0).

Definition lowcost_parent_match_by
    (g : G)
    (eligible_vertex : V -> Prop)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list E)
    (inf : Z) : Prop :=
  (forall v,
     In v (graph_vertices g) ->
     0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
    In v (graph_vertices g) ->
    eligible_vertex v ->
    (vertex_has_parent_edge_by g edge_for_vertex lowcost edge_parent inf v \/
     ((forall e, ~ edge_for_vertex v e) /\
      Znth v lowcost 0 = inf)).

Definition candidate_vertex
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) (v : V) : Prop :=
  In v (graph_vertices g) /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  vertex_has_parent_edge g s lowcost edge_parent inf v.

Definition candidate_vertex_exists_in_range
    (n : Z) (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) : Prop :=
  exists v,
    In v (Zrange 0 n) /\
    candidate_vertex g s lowcost edge_parent inf v.

Definition min_vertex_in_range
    (g : G) (s : St) (j : Z) (inf : Z)
    (minIndex : V) (lowcost : list Z) (edge_parent : list E) : Prop :=
  (minIndex = -1 /\
   forall v,
     In v (Zrange 0 j) ->
     ~ candidate_vertex g s lowcost edge_parent inf v) \/
  (candidate_vertex g s lowcost edge_parent inf minIndex /\
   In minIndex (Zrange 0 j) /\
   forall v,
     In v (Zrange 0 j) ->
     candidate_vertex g s lowcost edge_parent inf v ->
     Znth minIndex lowcost 0 <= Znth v lowcost 0).

Definition selected_parent_edge_is_min_cut_edge
    (g : G) (s : St) (edge_parent : list E) (minIndex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => Prim.is_cut_edge g s e)
    (weight g)
    (Znth minIndex edge_parent default_edge).

Definition selected_parent_pair
    (g : G) (s : St) (edge_parent : list E) (minIndex u v : V) : Prop :=
  let e := Znth minIndex edge_parent default_edge in
  v = minIndex /\
  vvalid s.(Prim.graph_in_state) u /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  step_aux g e u v.

Definition selected_parent_add_to_mst
    (g : G) (s s_next : St) (edge_parent : list E) (minIndex : V) : Prop :=
  exists u v,
    selected_parent_pair g s edge_parent minIndex u v /\
    addEdge s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
      u v (Znth minIndex edge_parent default_edge) /\
    s_next.(Prim.graph_in_state) =
      add_edge_graph s.(Prim.graph_in_state) u v
        (Znth minIndex edge_parent default_edge).

(** ** 扫描矩阵一行时对 [lowcost] 和 ghost [edge_parent] 的更新 *)

Definition scan_one_matrix_neighbor_update
    (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v v : V)
    (lowcost_in : list Z) (edge_parent_in : list E)
    (lowcost_out : list Z) (edge_parent_out : list E) : Prop :=
  ((~ vvalid s.(Prim.graph_in_state) v /\
    matrix_entry matrix from_v v <> inf /\
    matrix_entry matrix from_v v < Znth v lowcost_in 0 /\
    graph_step g (undirected_edge from_v v) from_v v /\
    weight g (undirected_edge from_v v) = Some (matrix_entry matrix from_v v) /\
    lowcost_out = replace_Znth v (matrix_entry matrix from_v v) lowcost_in /\
    edge_parent_out = replace_Znth v (undirected_edge from_v v) edge_parent_in) \/
   ((vvalid s.(Prim.graph_in_state) v \/
     matrix_entry matrix from_v v = inf \/
     Znth v lowcost_in 0 <= matrix_entry matrix from_v v) /\
	    lowcost_out = lowcost_in /\
	    edge_parent_out = edge_parent_in)).

Definition matrix_row_edge_for_vertex
    (g : G) (s : St) (from_v v : V) (e : E) : Prop :=
  is_cut_edge_to_vertex g s v e /\
  (edge_src g e = from_v \/ edge_dst g e = from_v).

Definition add_matrix_row_edge_for_vertex
    (g : G) (s : St) (from_v cur : V)
    (edge_for_vertex : V -> E -> Prop)
    (v : V) (e : E) : Prop :=
  edge_for_vertex v e \/
  (v = cur /\ matrix_row_edge_for_vertex g s from_v v e).

Fixpoint add_matrix_row_edges_for_vertex
    (g : G) (s : St) (from_v : V) (scanned : list V)
    (edge_for_vertex : V -> E -> Prop) : V -> E -> Prop :=
  match scanned with
  | nil => edge_for_vertex
  | cur :: rest =>
      add_matrix_row_edges_for_vertex g s from_v rest
        (add_matrix_row_edge_for_vertex g s from_v cur edge_for_vertex)
  end.

Inductive scan_matrix_row_update
    (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v : V)
    : list V -> list Z -> list E -> list Z -> list E -> Prop :=
| scan_matrix_row_update_nil :
    forall lowcost edge_parent,
      scan_matrix_row_update g matrix inf s from_v nil
        lowcost edge_parent lowcost edge_parent
| scan_matrix_row_update_cons :
    forall v rest lowcost0 edge_parent0 lowcost1 edge_parent1 lowcost2 edge_parent2,
      scan_one_matrix_neighbor_update g matrix inf s from_v v
        lowcost0 edge_parent0 lowcost1 edge_parent1 ->
      scan_matrix_row_update g matrix inf s from_v rest
        lowcost1 edge_parent1 lowcost2 edge_parent2 ->
      scan_matrix_row_update g matrix inf s from_v (v :: rest)
        lowcost0 edge_parent0 lowcost2 edge_parent2.

Definition scan_matrix_row_prefix_update
    (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v : V)
    (j : Z)
    (lowcost_in : list Z) (edge_parent_in : list E)
    (lowcost_out : list Z) (edge_parent_out : list E) : Prop :=
  scan_matrix_row_update g matrix inf s from_v (Zrange 0 j)
    lowcost_in edge_parent_in lowcost_out edge_parent_out.

Definition scan_matrix_row_full_update
    (n : Z) (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v : V)
    (lowcost_in : list Z) (edge_parent_in : list E)
    (lowcost_out : list Z) (edge_parent_out : list E) : Prop :=
  scan_matrix_row_prefix_update g matrix inf s from_v n
    lowcost_in edge_parent_in lowcost_out edge_parent_out.

