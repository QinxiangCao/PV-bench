Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.ClassicalDescription.
From ListLib.Base Require Import Positional.
Require Import ListLib.General.Length.
From SimpleC.SL Require Import IntLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import SetsClass.SetsClass.
From AUXLib Require Import ListLib.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
From GraphLib.examples Require Import prim.
From MonadLib.StateRelMonad Require Import StateRelHoare.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelMonad.
Require Algorithms.Prim.Prim.
Require Export PVbench.Algorithms.prim_forward_star_heap.rocq.forward_star_helper_lib.
Require Import PVbench.Algorithms.prim_forward_star_heap.rocq.priority_queue_helper_lib.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition selected_edges_range_state := parent_edges_range_state.
Definition selected_edges_exact_state := parent_edges_exact_state.
Definition selected_edges_match_state := parent_edges_match_state.
Definition return_is_mst (g rg : G) : Prop := is_mst g rg.

(** * Priority-queue decrease-key interface for Prim

    The C implementation now uses the shared decrease-key heap.  At the
    algorithm layer the heap is represented by a partial map from vertex
    ([data]) to current priority ([key]).
 *)

Definition partial_map_empty : partial_map := fun _ => None.

Definition prim_queue_map_initial
    (before after : partial_map) (vertex key : Z) : Prop :=
  before = partial_map_empty /\
  after = partial_map_add before vertex key.

Definition prim_queue_map_pop
    (before after : partial_map) (vertex key : Z) : Prop :=
  partial_map_minimum before (heap_item key vertex) /\
  after = partial_map_remove before vertex.

Definition prim_queue_map_update_or_push
    (before after : partial_map)
    (size_before size_after vertex key : Z) : Prop :=
  partial_map_update_or_add_size before size_before size_after vertex key /\
  after = partial_map_update_or_add before vertex key.

Definition prim_heap_map_matches_state
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (M : partial_map) : Prop :=
  (forall vertex key,
      partial_map_present M vertex key ->
      candidate_vertex g s lowcost edge_parent inf vertex /\
      key = Znth vertex lowcost 0) /\
  (forall vertex,
      candidate_vertex g s lowcost edge_parent inf vertex ->
      partial_map_present M vertex (Znth vertex lowcost 0)).

Definition candidate_vertex_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (v : V) : Prop :=
  In v (graph_vertices g) /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  Znth v edge_parent 0 <> -1 /\
  0 <= Znth v edge_parent 0 < 2 * graph_edge_count g /\
  Znth v lowcost 0 < inf /\
  min_object_of_subset Z_op_le
    (edge_for_vertex v) (weight g) (Znth v edge_parent 0 / 2) /\
  weight g (Znth v edge_parent 0 / 2) = Some (Znth v lowcost 0).

Definition prim_heap_map_matches_state_by
    (g : G) (s : St) (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (M : partial_map) : Prop :=
  (forall vertex key,
      partial_map_present M vertex key ->
      candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex /\
      key = Znth vertex lowcost 0) /\
  (forall vertex,
      candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex ->
      partial_map_present M vertex (Znth vertex lowcost 0)).

Definition prim_heap_map_pop_selects_min_vertex
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (M : partial_map) (key vertex : Z) : Prop :=
  partial_map_minimum M (heap_item key vertex) /\
  prim_heap_map_matches_state g s lowcost edge_parent inf M /\
  key = Znth vertex lowcost 0 /\
  min_vertex_in_range g s (Zlength lowcost) inf vertex lowcost edge_parent.

Definition partial_map_update_one_directed_edge
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z)
    (lowcost_in : list Z) (de : DE)
    (M_in M_out : partial_map) : Prop :=
  let v := Znth de to_new 0 in
  let w := Znth de wt_new 0 in
  (is_cut_edge_to_vertex g s_next v (de / 2) /\
   w < Znth v lowcost_in 0 /\
   M_out = partial_map_update_or_add M_in v w) \/
  ((~ is_cut_edge_to_vertex g s_next v (de / 2) \/
    Znth v lowcost_in 0 <= w) /\
   M_out = M_in).

Inductive scan_directed_edges_partial_map_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z) :
    list DE ->
    list Z -> list DE -> partial_map ->
    list Z -> list DE -> partial_map -> Prop :=
| scan_directed_edges_partial_map_update_nil :
    forall lowcost edge_parent M,
      scan_directed_edges_partial_map_update
        g s_next to_new wt_new nil
        lowcost edge_parent M
        lowcost edge_parent M
| scan_directed_edges_partial_map_update_cons :
    forall de rest
           lowcost0 edge_parent0 M0
           lowcost1 edge_parent1 M1
           lowcost2 edge_parent2 M2,
      scan_one_directed_edge_update
        g s_next to_new wt_new
        lowcost0 edge_parent0 de
        lowcost1 edge_parent1 ->
      partial_map_update_one_directed_edge
        g s_next to_new wt_new lowcost0 de M0 M1 ->
      scan_directed_edges_partial_map_update
        g s_next to_new wt_new rest
        lowcost1 edge_parent1 M1
        lowcost2 edge_parent2 M2 ->
      scan_directed_edges_partial_map_update
        g s_next to_new wt_new (de :: rest)
        lowcost0 edge_parent0 M0
        lowcost2 edge_parent2 M2.

Definition scan_minIndex_adjacency_map_prefix_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V) (current_e : DE)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (M_before : partial_map)
    (lowcost_current : list Z) (edge_parent_current : list DE)
    (M_current : partial_map) : Prop :=
  exists edge_for_base scanned_edges remaining_edges,
    is_first_link_chain link first minIndex (scanned_edges ++ remaining_edges) /\
    is_link_chain link current_e remaining_edges /\
    Permutation (scanned_edges ++ remaining_edges)
      (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before M_before
      lowcost_current edge_parent_current M_current /\
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      (add_scanned_edges_for_vertex g s_next to_new edge_for_base scanned_edges)
      lowcost_current edge_parent_current 1000000000 /\
    prim_heap_map_matches_state_by
      g s_next
      (add_scanned_edges_for_vertex g s_next to_new edge_for_base scanned_edges)
      lowcost_current edge_parent_current 1000000000 M_current /\
    (forall v e,
      ~ vvalid s_next.(Prim.graph_in_state) v ->
      add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex edge_for_base v e <->
      is_cut_edge_to_vertex g s_next v e).

Definition scan_minIndex_adjacency_map_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (M_before : partial_map)
    (lowcost_after : list Z) (edge_parent_after : list DE)
    (M_after : partial_map) : Prop :=
  scan_minIndex_adjacency_update
    g s_next from_new first link to_new wt_new minIndex
    lowcost_before edge_parent_before lowcost_after edge_parent_after /\
  prim_heap_map_matches_state
    g s_next lowcost_after edge_parent_after 1000000000 M_after.

Definition prim_heap_loop_state
    (g : G) (src : V) (chosen : Z) (s : St)
    (lowcost visited edge_parent : list Z) (M : partial_map)
    (X : unit -> St -> Prop) : Prop :=
  (chosen = 0 /\
   s = initSt g src /\
   lowcost =
     replace_Znth src 0
       (repeat 1000000000 (Z.to_nat (Zlength lowcost))) /\
   visited = repeat 0 (Z.to_nat (Zlength visited)) /\
   edge_parent = repeat (-1) (Z.to_nat (Zlength edge_parent)) /\
   M = partial_map_add partial_map_empty src 0 /\
   safeExec (initStPred g src) (Prim2 g) X) \/
  (1 <= chosen /\
   growing_subgraph_state g s /\
   visited_matches_state g s visited /\
   state_vertex_count s = chosen /\
   selected_edges_match_state g src s edge_parent /\
   lowcost_parent_match g s lowcost edge_parent 1000000000 /\
   prim_heap_map_matches_state g s lowcost edge_parent 1000000000 M /\
   safeExec (prim_state_is s) (Prim2_loop g (chosen - 1)) X).

Definition prim_heap_after_pop_state
    (g : G) (src : V) (chosen : Z) (s : St)
    (lowcost visited edge_parent : list Z)
    (M_before M_after : partial_map) (minIndex minCost : Z)
    (X : unit -> St -> Prop) : Prop :=
  prim_heap_loop_state g src chosen s lowcost visited edge_parent M_before X /\
  prim_queue_map_pop M_before M_after minIndex minCost /\
  ((chosen = 0 /\ minIndex = src /\ minCost = 0 /\ s = initSt g src) \/
   (1 <= chosen /\
    prim_heap_map_pop_selects_min_vertex
      g s lowcost edge_parent 1000000000 M_before minCost minIndex)).

Definition prim_heap_scan_state
    (g : G) (src : V) (chosen : Z) (s_before s_after : St)
    (from_new first link to_new weight_new : list Z)
    (lowcost_before visited_after edge_parent_before : list Z)
    (lowcost_current edge_parent_current : list Z)
    (current_e minIndex minCost : Z)
    (M_before : partial_map)
    (lowcost_out edge_parent_out : list Z) (M_current : partial_map)
    (X : unit -> St -> Prop) : Prop :=
  1 <= chosen /\
  growing_subgraph_state g s_after /\
  visited_matches_state g s_after visited_after /\
  state_vertex_count s_after = chosen /\
  selected_edges_match_state g src s_after edge_parent_before /\
  scan_minIndex_adjacency_map_prefix_update
    g s_after from_new first link to_new weight_new minIndex current_e
    lowcost_before edge_parent_before M_before
    lowcost_current edge_parent_current M_current /\
  lowcost_out = lowcost_current /\
  edge_parent_out = edge_parent_current /\
  safeExec (prim_state_is s_after) (Prim2_loop g (chosen - 1)) X.

Definition prim_heap_done_state
    (g : G) (src : V) (s : St)
    (lowcost visited edge_parent : list Z) (M : partial_map)
    (X : unit -> St -> Prop) : Prop :=
  growing_subgraph_state g s /\
  visited_matches_state g s visited /\
  state_vertex_count s = Zlength lowcost /\
  selected_edges_match_state g src s edge_parent /\
  lowcost_parent_match g s lowcost edge_parent 1000000000 /\
  prim_heap_map_matches_state g s lowcost edge_parent 1000000000 M /\
  safeExec (prim_state_is s) (return tt) X.

Lemma add_edge_graph_gvalid_any :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    vvalid g v ->
    ~ evalid g e ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hv Hne.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  rewrite add_edge_graph_evalid in Ha by auto.
  destruct Ha as [Ha | ->].
  - destruct (Hg a Ha) as [x [y Hstep]].
    exists x, y.
    rewrite add_edge_graph_step by auto.
    left; exact Hstep.
  - exists u, v.
    rewrite add_edge_graph_step by auto.
    right; split; [reflexivity|auto].
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
  destruct (proj1 (remove_edge_graph_step g u v e x y a Hg Hstep) Hstep_a)
    as [Hremove | [Ha_eq Hnew]].
  - exists x, y; exact Hremove.
  - contradiction.
Qed.

#[export] Instance addEdgeInSubgraph_instance :
  addEdgeInSubgraph G V E.
Proof.
  constructor.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hv Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid_any; auto.
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
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
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

Record multiset (A : Type) : Type := {
  mlist : list A
}.

Arguments mlist {A} _.

Definition list_to_multiset {A} (l : list A) : multiset A :=
  {| mlist := l |}.

Definition multiset_empty {A} : multiset A :=
  list_to_multiset [].

Definition multiset_size {A} (S : multiset A) : Z :=
  Zlength (mlist S).

Definition multiset_insert {A}
    (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (x :: mlist S).

Definition multiset_remove {A}
    (S : multiset A) (x : A) : multiset A :=
  let fix remove_one (l : list A) : list A :=
    match l with
    | [] => []
    | y :: ys =>
        if excluded_middle_informative (x = y)
        then ys
        else y :: remove_one ys
    end
  in list_to_multiset (remove_one (mlist S)).

(** * 双数组最小堆模型

    这部分仿照 [LLM_bench/Data_structures/priority_queue]，但 Prim 需要
    存二元信息：cost 是当前候选代价，vertex 是候选点编号。因此 C 中使用
    两个数组 [heap_cost] 和 [heap_vertex]，逻辑层用 [(cost, vertex)] 列表描述。

    本区命名尽量和 [priority_queue_lib.v] 对齐，并统一加 [Pair] 后缀表示
    “双数组一起移动”的版本。 *)

Definition HeapEntry : Type := (Z * V)%type.

(** [IntArray.full] 存储的每个元素都是合法 int。 *)

(** [IntArray.full] 存储的每个元素都是合法 int（全局版）。 *)

Definition HeapParent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Definition HeapEntriesPair
    (heap_cost heap_vertex : list Z) (n : Z) : list HeapEntry :=
  map
    (fun idx => (Znth idx heap_cost 0, Znth idx heap_vertex 0))
    (Zrange 0 n).

Definition MinHeapPrefixPair
    (heap_cost heap_vertex : list Z) (n : Z) : Prop :=
  0 <= n /\
  n <= Zlength heap_cost /\
  n <= Zlength heap_vertex /\
  forall child,
    0 < child /\ child < n ->
    Znth (HeapParent child) heap_cost 0 <= Znth child heap_cost 0.

Definition PrefixMinValuePair
    (entries : list HeapEntry) (cost : Z) (vertex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun entry => In entry entries)
    (fun entry => Some (fst entry))
    (cost, vertex).

Definition PriorityQueuePrefixPair
    (heap_cost heap_vertex : list Z) (n : Z) (entries : list HeapEntry) : Prop :=
  entries = HeapEntriesPair heap_cost heap_vertex n /\
  MinHeapPrefixPair heap_cost heap_vertex n /\
  (0 < n ->
   PrefixMinValuePair entries
     (Znth 0 heap_cost 0)
     (Znth 0 heap_vertex 0)).

(** 堆中保存的 vertex 都是 C 程序可访问的点编号。 *)
Definition HeapEntriesVertexRangePair (bound : Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    0 <= vertex < bound.

(** 新版 priority_queue 风格的 pair 堆抽象。

    [multiset] 只描述堆里“有哪些 entry”，不描述数组顺序；
    [heap_representation_pair] 才把这个 multiset 和两条 C 数组前缀联系起来，
    并要求前缀满足最小堆序。这样 push/pop 的规格就不用偷看调用前
    [heap_size] 位置的数组值。 *)
Definition HeapEntrySet : Type := multiset HeapEntry.

Definition empty_heap_entry_set : HeapEntrySet := multiset_empty.

Definition heap_entry_set_insert
    (S : HeapEntrySet) (cost vertex : Z) : HeapEntrySet :=
  multiset_insert S (cost, vertex).

Definition heap_entry_eq_dec (x y : HeapEntry) : {x = y} + {x <> y}.
Proof.
  decide equality; apply Z.eq_dec.
Defined.

Definition heap_entry_set_remove
    (S : HeapEntrySet) (cost vertex : Z) : HeapEntrySet :=
  let fix remove_one (l : list HeapEntry) : list HeapEntry :=
    match l with
    | [] => []
    | (entry_cost, entry_vertex) :: rest =>
        if Z.eq_dec cost entry_cost
        then if Z.eq_dec vertex entry_vertex
             then rest
             else (entry_cost, entry_vertex) :: remove_one rest
        else (entry_cost, entry_vertex) :: remove_one rest
    end
  in list_to_multiset (remove_one (mlist S)).

Definition heap_entry_set_minimum
    (S : HeapEntrySet) (cost vertex : Z) : Prop :=
  In (cost, vertex) (mlist S) /\
  forall cost' vertex',
    In (cost', vertex') (mlist S) ->
    cost <= cost'.

Definition heap_entries_to_set (entries : list HeapEntry) : HeapEntrySet :=
  list_to_multiset entries.

Definition heap_relation_pair
    (S : HeapEntrySet) (heap_cost heap_vertex : list Z) (size : Z) : Prop :=
  Permutation (mlist S) (HeapEntriesPair heap_cost heap_vertex size).

Definition heap_representation_pair
    (S : HeapEntrySet) (heap_cost heap_vertex : list Z) (size : Z) : Prop :=
  0 <= size /\
  Zlength heap_cost = size /\
  Zlength heap_vertex = size /\
  multiset_size S = size /\
  heap_relation_pair S heap_cost heap_vertex size /\
  MinHeapPrefixPair heap_cost heap_vertex size.

Definition store_heap_pair
    (heap_cost_ptr heap_vertex_ptr : Z) (S : HeapEntrySet) (size : Z)
    : Assertion :=
  EX heap_cost : list Z, EX heap_vertex : list Z,
    “ heap_representation_pair S heap_cost heap_vertex size ” &&
    IntArray.full heap_cost_ptr size heap_cost **
    IntArray.full heap_vertex_ptr size heap_vertex.

Definition heap_spare_pair
    (heap_cost_ptr heap_vertex_ptr size : Z) : Assertion :=
  IntArray.undef_seg heap_cost_ptr size (size + 1) **
  IntArray.undef_seg heap_vertex_ptr size (size + 1).

Definition PushSourcePair
    (written_cost written_vertex : list Z)
    (before : HeapEntrySet) (size cost vertex : Z) : Prop :=
  Zlength written_cost = size + 1 /\
  Zlength written_vertex = size + 1 /\
  Permutation
    (HeapEntriesPair written_cost written_vertex (size + 1))
    ((cost, vertex) :: mlist before) /\
  MinHeapPrefixPair written_cost written_vertex size.

Definition PushResultPair
    (before : HeapEntrySet) (result_cost result_vertex : list Z)
    (size cost vertex : Z) : Prop :=
  0 <= size /\
  Zlength result_cost = size + 1 /\
  Zlength result_vertex = size + 1 /\
  Permutation
    (HeapEntriesPair result_cost result_vertex (size + 1))
    ((cost, vertex) :: mlist before) /\
  MinHeapPrefixPair result_cost result_vertex (size + 1).

Definition HeapOrderExceptUpPair
    (heap_cost : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (HeapParent node) heap_cost 0 <= Znth node heap_cost 0.

Definition PushHoleChildrenPreservedPair
    (heap_cost : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node /\ node < size /\ HeapParent node = child ->
    Znth (HeapParent child) heap_cost 0 <= Znth node heap_cost 0.

Definition PushLoopStatePair
    (written_cost written_vertex cost_cur vertex_cur : list Z)
    (size child cost vertex : Z) : Prop :=
  0 <= size /\
  Zlength written_cost = size + 1 /\
  Zlength written_vertex = size + 1 /\
  Zlength cost_cur = size + 1 /\
  Zlength vertex_cur = size + 1 /\
  0 <= child /\
  child <= size /\
  Znth child cost_cur 0 = cost /\
  Znth child vertex_cur 0 = vertex /\
  Permutation
    (HeapEntriesPair written_cost written_vertex (size + 1))
    (HeapEntriesPair cost_cur vertex_cur (size + 1)) /\
  HeapOrderExceptUpPair cost_cur (size + 1) child /\
  PushHoleChildrenPreservedPair cost_cur (size + 1) child.

Definition PopResultPairCore
    (cost_before vertex_before cost_after vertex_after : list Z)
    (n cost vertex : Z) : Prop :=
  1 <= n /\
  Zlength cost_before = n /\
  Zlength vertex_before = n /\
  Zlength cost_after = n /\
  Zlength vertex_after = n /\
  PriorityQueuePrefixPair
    cost_before vertex_before n
    (HeapEntriesPair cost_before vertex_before n) /\
  PrefixMinValuePair
    (HeapEntriesPair cost_before vertex_before n) cost vertex /\
  cost = Znth 0 cost_before 0 /\
  vertex = Znth 0 vertex_before 0 /\
  Znth (n - 1) cost_after 0 = cost /\
  Znth (n - 1) vertex_after 0 = vertex /\
  PriorityQueuePrefixPair
    cost_after vertex_after (n - 1)
    (HeapEntriesPair cost_after vertex_after (n - 1)) /\
  Permutation
    (HeapEntriesPair cost_before vertex_before n)
    ((cost, vertex) :: HeapEntriesPair cost_after vertex_after (n - 1)).

Definition PopResultPair
    (S_before : HeapEntrySet)
    (cost_before vertex_before cost_after vertex_after : list Z)
    (n cost vertex : Z) : Prop :=
  heap_representation_pair S_before cost_before vertex_before n /\
  heap_entry_set_minimum S_before cost vertex /\
  PopResultPairCore cost_before vertex_before cost_after vertex_after
    n cost vertex.

Definition HeapOrderExceptDownPair
    (heap_cost : list Z) (size idx : Z) : Prop :=
  0 <= idx /\
  idx < size /\
  forall child,
    0 < child /\ child < size /\ HeapParent child <> idx ->
    Znth (HeapParent child) heap_cost 0 <= Znth child heap_cost 0.

Definition PopHoleParentDominatesChildrenPair
    (heap_cost : list Z) (size idx : Z) : Prop :=
  idx = 0 \/
  forall child,
    0 < child /\ child < size /\ HeapParent child = idx ->
    Znth (HeapParent idx) heap_cost 0 <= Znth child heap_cost 0.

Definition PopSelectedChildPair
    (heap_cost : list Z) (size idx smallest : Z) : Prop :=
  0 <= idx /\
  idx < size /\
  idx < smallest /\
  0 <= smallest /\
  smallest < size /\
  HeapParent smallest = idx /\
  (forall child,
     0 < child /\ child < size /\ HeapParent child = idx ->
     Znth smallest heap_cost 0 <= Znth child heap_cost 0).

Definition PopLoopStatePair
    (cost_before vertex_before cost_cur vertex_cur : list Z)
  (n idx : Z) : Prop :=
  1 < n /\
  Zlength cost_before = n /\
  Zlength vertex_before = n /\
  Zlength cost_cur = n /\
  Zlength vertex_cur = n /\
  0 <= idx /\
  idx < n - 1 /\
  PriorityQueuePrefixPair
    cost_before vertex_before n
    (HeapEntriesPair cost_before vertex_before n) /\
  Znth idx cost_cur 0 = Znth (n - 1) cost_before 0 /\
  Znth idx vertex_cur 0 = Znth (n - 1) vertex_before 0 /\
  Znth (n - 1) cost_cur 0 = Znth (n - 1) cost_before 0 /\
  Znth (n - 1) vertex_cur 0 = Znth (n - 1) vertex_before 0 /\
  1 <= n /\
  n <= Zlength cost_before /\
  n <= Zlength vertex_before /\
  n <= Zlength cost_cur /\
  n <= Zlength vertex_cur /\
  Permutation
    (HeapEntriesPair cost_cur vertex_cur (n - 1))
    (sublist 1 n (HeapEntriesPair cost_before vertex_before n)) /\
  HeapOrderExceptDownPair cost_cur (n - 1) idx /\
  PopHoleParentDominatesChildrenPair cost_cur (n - 1) idx.

Definition PopReadyStatePair
    (cost_before vertex_before cost_cur vertex_cur : list Z)
  (n cost vertex : Z) : Prop :=
  1 < n /\
  Zlength cost_before = n /\
  Zlength vertex_before = n /\
  Zlength cost_cur = n /\
  Zlength vertex_cur = n /\
  PriorityQueuePrefixPair
    cost_before vertex_before n
    (HeapEntriesPair cost_before vertex_before n) /\
  PrefixMinValuePair
    (HeapEntriesPair cost_before vertex_before n) cost vertex /\
  cost = Znth 0 cost_before 0 /\
  vertex = Znth 0 vertex_before 0 /\
  Znth (n - 1) cost_cur 0 = Znth (n - 1) cost_before 0 /\
  Znth (n - 1) vertex_cur 0 = Znth (n - 1) vertex_before 0 /\
  1 <= n /\
  n <= Zlength cost_before /\
  n <= Zlength vertex_before /\
  n <= Zlength cost_cur /\
  n <= Zlength vertex_cur /\
  Permutation
    (HeapEntriesPair cost_cur vertex_cur (n - 1))
    (sublist 1 n (HeapEntriesPair cost_before vertex_before n)) /\
  PriorityQueuePrefixPair
    cost_cur vertex_cur (n - 1)
    (HeapEntriesPair cost_cur vertex_cur (n - 1)).

(** * 堆与 Prim的关系 *)
  
Definition heap_entry_matches_candidate
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entry : HeapEntry) : Prop :=
  let '(cost, vertex) := entry in
  candidate_vertex g s lowcost edge_parent inf vertex /\
  cost = Znth vertex lowcost 0.

Definition heap_contains_all_candidates
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall vertex,
    candidate_vertex g s lowcost edge_parent inf vertex ->
    exists cost,
      In (cost, vertex) entries /\
      cost = Znth vertex lowcost 0.

Definition heap_current_entries_are_candidates
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    cost = Znth vertex lowcost 0 ->
    candidate_vertex g s lowcost edge_parent inf vertex.

Definition heap_entries_respect_lowcost
    (lowcost : list Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    Znth vertex lowcost 0 <= cost.

Definition heap_matches_prim_state
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  heap_contains_all_candidates g s lowcost edge_parent inf entries /\
  heap_current_entries_are_candidates g s lowcost edge_parent inf entries /\
  heap_entries_respect_lowcost lowcost entries /\
  NoDup entries.

(** 一条有向边在 lazy heap 中对应的候选 entry。 *)
Definition heap_entry_of_directed_edge
    (to_new : list DE) (wt_new : list Z) (de : DE) : HeapEntry :=
  (Znth de wt_new 0, Znth de to_new 0).

(** 堆 entry 的来源：lazy heap 不删除旧候选，所以堆大小不能只靠当前候选点数
    控制。真正的容量事实是：每个堆 entry 要么是初始的 [(0, src)]，
    要么来自某条有向边 [de] 被扫描时压入的
    [(weight_new[de], to_new[de])]。这个谓词只记录来源，不记录具体扫描顺序。 *)
Definition heap_entries_from_graph_edges
    (g : G) (src : V) (to_new : list DE) (wt_new : list Z)
    (entries : list HeapEntry) : Prop :=
  incl entries
    ((0, src) ::
       map (heap_entry_of_directed_edge to_new wt_new)
           (Zrange 0 (2 * graph_edge_count g))).

Definition current_heap_min_entry
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry)
    (cost : Z) (vertex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun entry =>
       In entry entries /\
       heap_entry_matches_candidate g s lowcost edge_parent inf entry)
    (fun entry => Some (fst entry))
    (cost, vertex).

Definition heap_pop_selects_min_vertex
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry)
    (cost : Z) (vertex : V) : Prop :=
  current_heap_min_entry g s lowcost edge_parent inf entries cost vertex /\
  min_object_of_subset Z_op_le
    (fun v => candidate_vertex g s lowcost edge_parent inf v)
    (fun v => Some (Znth v lowcost 0))
    vertex.

(** 把 [minIndex] 标记为 visited 后，其他顶点在 [s_before]/[s_after]
    中的 vvalid 状态等价。 *)

(** * 扫描邻接链时把新候选同步放进堆

    主循环扫描 [minIndex] 的邻接链时，每当一条有向边把某个顶点的
    [lowcost] 从 [inf] 或更大值压低成新的权重，就要把
    [(new_weight, vertex)] 推进堆。扫描前缀只描述了 [lowcost]/[edge_parent]
    怎么随扫描变化，还需要同时记录堆的前缀更新，扫描到 -1 之后才能推出
    完整的 [heap_matches_prim_state]。 *)

(** 扫描一条有向边时，堆的更新：若该边触发 [lowcost] 更新，则把
    [(weight, vertex)] 推进堆；否则堆不变。 *)
Definition heap_update_one_directed_edge
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z)
    (lowcost_in : list Z) (de : DE)
    (heap_entries_in heap_entries_out : list HeapEntry) : Prop :=
  let v := Znth de to_new 0 in
  let w := Znth de wt_new 0 in
  (is_cut_edge_to_vertex g s_next v (de / 2) /\
   w < Znth v lowcost_in 0 /\
   Permutation heap_entries_out ((w, v) :: heap_entries_in)) \/
  ((~ is_cut_edge_to_vertex g s_next v (de / 2) \/
    Znth v lowcost_in 0 <= w) /\
   heap_entries_out = heap_entries_in).

(** 扫描一串有向边时，[lowcost]/[edge_parent]/堆 的并行更新。
    这一版把三个分量放在同一个归纳里，避免证明时还要手工对齐两条链。 *)
Inductive scan_directed_edges_full_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z) :
    list DE ->
    list Z -> list DE -> list HeapEntry ->
    list Z -> list DE -> list HeapEntry -> Prop :=
| scan_directed_edges_full_update_nil :
    forall lowcost edge_parent heap_entries,
      scan_directed_edges_full_update
        g s_next to_new wt_new nil
        lowcost edge_parent heap_entries
        lowcost edge_parent heap_entries
| scan_directed_edges_full_update_cons :
    forall de rest
           lowcost0 edge_parent0 heap_entries0
           lowcost1 edge_parent1 heap_entries1
           lowcost2 edge_parent2 heap_entries2,
      scan_one_directed_edge_update
        g s_next to_new wt_new
        lowcost0 edge_parent0 de lowcost1 edge_parent1 ->
      heap_update_one_directed_edge
        g s_next to_new wt_new lowcost0 de heap_entries0 heap_entries1 ->
      scan_directed_edges_full_update
        g s_next to_new wt_new rest
        lowcost1 edge_parent1 heap_entries1
        lowcost2 edge_parent2 heap_entries2 ->
      scan_directed_edges_full_update
        g s_next to_new wt_new (de :: rest)
        lowcost0 edge_parent0 heap_entries0
        lowcost2 edge_parent2 heap_entries2.

(** 扫描 [minIndex] 邻接链的前缀时，lowcost/edge_parent/堆 的并行更新。
    与 [scan_minIndex_adjacency_prefix_update] 结构一致，只是额外带堆。 *)
Definition scan_minIndex_adjacency_heap_prefix_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V) (current_e : DE)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (heap_entries_before : list HeapEntry)
    (lowcost_current : list Z) (edge_parent_current : list DE)
    (heap_entries_current : list HeapEntry) : Prop :=
  exists scanned_edges remaining_edges : list DE,
    is_first_link_chain link first minIndex (scanned_edges ++ remaining_edges) /\
    is_link_chain link current_e remaining_edges /\
    Permutation (scanned_edges ++ remaining_edges)
      (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_full_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before heap_entries_before
      lowcost_current edge_parent_current heap_entries_current.

(** 扫描完 [minIndex] 的全部邻接边后（[current_e = -1]），
    lowcost/edge_parent/堆 的完整更新。 *)
Definition scan_minIndex_adjacency_heap_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (heap_entries_before : list HeapEntry)
    (lowcost_after : list Z) (edge_parent_after : list DE)
    (heap_entries_after : list HeapEntry) : Prop :=
  exists scanned_edges : list DE,
    is_first_link_chain link first minIndex scanned_edges /\
    Permutation scanned_edges (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_full_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before heap_entries_before
      lowcost_after edge_parent_after heap_entries_after.

(** 参数化版本的候选点：把 [is_min_cut_edge_to_vertex] 换成
    “在 [edge_for_vertex] 集合中权重最小的边”。扫描过程中该集合只包含
    已经扫描过的边，扫描完成后实例化回真正的 min-cut 边。 *)
Definition heap_contains_all_candidates_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall vertex,
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex ->
    exists cost,
      In (cost, vertex) entries /\
      cost = Znth vertex lowcost 0.

Definition heap_current_entries_are_candidates_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    cost = Znth vertex lowcost 0 ->
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex.

Definition heap_matches_prim_state_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  heap_contains_all_candidates_by g s edge_for_vertex lowcost edge_parent inf entries /\
  heap_current_entries_are_candidates_by g s edge_for_vertex lowcost edge_parent inf entries /\
  heap_entries_respect_lowcost lowcost entries /\
  NoDup entries.

(** 把 [minIndex] 标记为 visited 后，其他顶点在 [s_before] 下的候选性
    等价于在 [s_after] 下、只考虑 [s_before] cut 边的参数化候选性。 *)

(** pop 出被选中的最小候选并把 [minIndex] 标记为 visited 后，
    pop 后的堆匹配 [s_after]（只考虑 [s_before] 的 cut 边）。 *)

(** 把非参数化的 heap 匹配实例化成参数化版本（edge_for_vertex =
    is_cut_edge_to_vertex）。 *)

(** 从 [lowcost_parent_match_by] 的 eligible 分支恢复参数化候选点。 *)

(** 在 edge_for_vertex 集合里加入一条权重不更优的边，不改变最小元。 *)

(** 若扫描边指向的顶点与候选顶点不同，则把它加入 edge_for_vertex
    不改变候选。 *)

(** 若候选顶点不是扫描边指向的顶点，则把该扫描边加入
    edge_for_vertex 不改变候选（正向）。 *)

(** 若某个顶点在扫描边中未被更新（lowcost/edge_parent 的 Znth 不变），
    则其候选性不变。 *)

(** 若扫描边不触发更新，则把它加入 edge_for_vertex 不改变候选。 *)

(** 若扫描边不触发更新（要么不是 cut edge，要么权重不更优），
    则把它加入 edge_for_vertex 不改变候选（正向）。 *)

(** 若扫描边不触发更新，则把它加入 edge_for_vertex 不改变候选。 *)

(** 把列表某个位置的值改成更小的值后，任意位置的 [Znth] 都不会变大。 *)

(** 单条有向边扫描后，[heap_entries_respect_lowcost] 保持。 *)

(** 扫描一条有向边后，参数化 heap 匹配保持。 *)

(** 单条有向边扫描后，堆里 entry 的顶点范围保持。 *)

(** 扫描只会往堆里加条目，不会删除：扫描前堆的条目都在扫描后堆里。 *)

(** 扫描邻接边时，堆只会在严格改进 lowcost 的情况下加入新 entry；
    因此若扫描前堆条目无重复，则扫描后仍无重复。 *)

(** 扫描一串有向边后，参数化 heap 匹配保持（归纳）。 *)

(** 扫描 [minIndex] 邻接链到 -1 后，前缀更新退化为完整更新。 *)

(** 在已扫描列表末尾追加一条边：先扫描 [l]，再扫描 [de]。 *)

(** 扫描前缀从 [cur_edge] 推进到 [link[cur_edge]]：当前边被处理后，
    lowcost/edge_parent/堆 的前缀更新同时前进。 *)

(** 扫描完成后，把参数化 heap 匹配里的候选边集合换回
    [is_cut_edge_to_vertex]。 *)

(** 反方向：把参数化版本实例化回非参数化的 heap 匹配。 *)

(** 扫描完 [minIndex] 的全部邻接边后，堆匹配完整 Prim 状态。 *)

(** 初始状态（[chosen = 1]，首次扫描 [src] 的邻边）下，扫描完成后堆匹配
    [s_after]（即 [initSt g src]）。base 用空边集合 + 空堆。 *)

(** 扫描 [minIndex] 邻接链的起点：0 条边已扫描时，lowcost/edge_parent/
    堆都不变。 *)

