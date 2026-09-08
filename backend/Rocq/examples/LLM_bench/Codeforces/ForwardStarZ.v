(** * Forward-star adjacency, as a Z-indexed pure model.

    A forward star stores an undirected or directed graph in flat integer
    arrays: [head_values] gives, for each vertex, the index of the first edge
    leaving it (or [-1]); [next_values] links each edge to the next one out of
    the same vertex (or [-1]); [to_values] holds each edge's far endpoint.  The
    C programs in this benchmark build exactly that in [head] / [nxt] / [to],
    and several of them attach a per-edge payload in a fourth array.

    Nothing here is an [Assertion].  The arrays themselves are owned by the
    ordinary array predicates in the C annotation; this file only relates the
    *contents* of the ghost lists to the graph they encode, which is what a
    loop invariant needs.  That is the same division the Dijkstra development
    uses -- see [Algorithms/Dijkstra/Dijkstra_linked_forward_star_lib.v], from
    which the chain relation and the edge-set iteration scheme below are
    adapted.

    Two differences from that development make it unusable here directly, and
    both are why this file exists:

    - it fixes vertices to [0 <= i < DijkstraGraph.max_vertices] with
      [max_vertices = 10], while these problems have up to [5 * 10^5] and
      number their vertices from [1];
    - it ties the model to [edge_weight : V -> V -> option Z], a *function*,
      which cannot represent parallel edges -- and at least one problem here
      states that repeated edges between the same pair may occur.

    So the vertex range is a parameter [vok] throughout, and no graph
    correspondence is fixed: each specification states its own against its own
    logical object (an edge list, a comment list, a tree). *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(** ** Chasing the next-links *)

(** [next_chain ns start idx]: following [next_values] from edge [start],
    without passing [-1], reaches edge [idx].  Reflexive at [start]. *)
Inductive next_chain (ns : list Z) : Z -> Z -> Prop :=
  | next_chain_here : forall e,
      0 <= e < Zlength ns ->
      next_chain ns e e
  | next_chain_next : forall cur e,
      0 <= cur < Zlength ns ->
      Znth cur ns (-1) <> -1 ->
      next_chain ns (Znth cur ns (-1)) e ->
      next_chain ns cur e.

Lemma next_chain_bounds :
  forall ns start idx, next_chain ns start idx -> 0 <= start < Zlength ns.
Proof. induction 1; auto. Qed.

Lemma next_chain_target_bounds :
  forall ns start idx, next_chain ns start idx -> 0 <= idx < Zlength ns.
Proof. induction 1; auto. Qed.

Lemma next_chain_minus_one_false :
  forall ns idx, ~ next_chain ns (-1) idx.
Proof.
  intros ns idx H. apply next_chain_bounds in H. lia.
Qed.

Lemma next_chain_trans :
  forall ns start mid idx,
    next_chain ns start mid -> next_chain ns mid idx -> next_chain ns start idx.
Proof.
  intros ns start mid idx H. revert idx. induction H; intros idx Hmid; auto.
  apply next_chain_next; auto.
Qed.

Lemma next_chain_tail_to_head :
  forall ns edge idx,
    0 <= edge < Zlength ns ->
    Znth edge ns (-1) <> -1 ->
    next_chain ns (Znth edge ns (-1)) idx ->
    next_chain ns edge idx.
Proof. intros. apply next_chain_next; auto. Qed.

(** A chain from [start] either stops there or goes on through the successor. *)
Lemma next_chain_inv :
  forall ns start idx,
    next_chain ns start idx ->
    idx = start \/
    (Znth start ns (-1) <> -1 /\ next_chain ns (Znth start ns (-1)) idx).
Proof. induction 1; auto. Qed.

(** ** Well-formedness of the arrays *)

(** [vok] is the caller's vertex predicate: [fun v => 1 <= v <= n] for the
    1-based problems, [fun v => 0 <= v < n] for 0-based ones. *)

Definition head_values_safe
    (vok : Z -> Prop) (edge_count : Z) (hs : list Z) : Prop :=
  forall u, vok u ->
    0 <= u < Zlength hs /\
    (Znth u hs (-1) = -1 \/ 0 <= Znth u hs (-1) < edge_count).

Definition edge_values_safe
    (vok : Z -> Prop) (edge_count : Z) (ts ns : list Z) : Prop :=
  Zlength ts = edge_count /\ Zlength ns = edge_count /\
  forall e, 0 <= e < edge_count ->
    vok (Znth e ts 0) /\
    (Znth e ns (-1) = -1 \/ 0 <= Znth e ns (-1) < edge_count).

(** No chain revisits an edge, and a vertex's list holds each edge once. *)
Definition forward_star_chain_wf (vok : Z -> Prop) (hs ns : list Z) : Prop :=
  (forall e,
     0 <= e < Zlength ns ->
     Znth e ns (-1) <> -1 ->
     ~ next_chain ns (Znth e ns (-1)) e) /\
  (forall u i j,
     vok u ->
     next_chain ns (Znth u hs (-1)) i ->
     next_chain ns (Znth u hs (-1)) j ->
     i = j \/ next_chain ns i j \/ next_chain ns j i).

(** ** Which edges a vertex owns *)

(** [outgoing ... u e]: edge index [e] is on [u]'s list. *)
Definition outgoing (hs ns : list Z) (u e : Z) : Prop :=
  next_chain ns (Znth u hs (-1)) e.

(** [suffix ... cursor e]: [e] is still ahead of, or at, the cursor.  This is
    the "not yet visited" half of an adjacency-list walk. *)
Definition suffix (ns : list Z) (cursor e : Z) : Prop :=
  cursor <> -1 /\ next_chain ns cursor e.

(** [done ... u cursor e]: [e] belongs to [u] and is already behind the
    cursor.  Together with [suffix] this partitions [u]'s edge list, which is
    the shape an edge-scanning loop invariant wants. *)
Definition done (hs ns : list Z) (u cursor e : Z) : Prop :=
  outgoing hs ns u e /\ ~ suffix ns cursor e.

Lemma suffix_minus_one_empty :
  forall ns e, ~ suffix ns (-1) e.
Proof. intros ns e [Hne _]. congruence. Qed.

(** At the start of a walk nothing is done. *)
Lemma done_at_head_empty :
  forall hs ns u,
    Znth u hs (-1) <> -1 ->
    forall e, ~ done hs ns u (Znth u hs (-1)) e.
Proof.
  intros hs ns u Hhead e [Hout Hnot]. apply Hnot. split; auto.
Qed.

(** At the end of a walk everything outgoing is done. *)
Lemma done_at_end_all :
  forall hs ns u e, outgoing hs ns u e -> done hs ns u (-1) e.
Proof.
  intros hs ns u e Hout. split; [exact Hout |]. apply suffix_minus_one_empty.
Qed.

(** The cursor itself is outgoing, and not yet done. *)
Lemma cursor_outgoing :
  forall hs ns u cursor,
    cursor <> -1 ->
    next_chain ns (Znth u hs (-1)) cursor ->
    outgoing hs ns u cursor /\ ~ done hs ns u cursor cursor.
Proof.
  intros hs ns u cursor Hne Hchain. split; [exact Hchain |].
  intros [_ Hnot]. apply Hnot. split; [exact Hne |].
  apply next_chain_here. eapply next_chain_target_bounds; eauto.
Qed.

(** Advancing the cursor by one link moves exactly the cursor edge from the
    suffix to the done part.  This is the step every edge-scanning loop takes. *)
Lemma done_step :
  forall hs ns u cursor e,
    0 <= cursor < Zlength ns ->
    cursor <> -1 ->
    next_chain ns (Znth u hs (-1)) cursor ->
    forward_star_chain_wf (fun _ => True) hs ns ->
    (done hs ns u (Znth cursor ns (-1)) e <->
       done hs ns u cursor e \/ e = cursor).
Proof.
  intros hs ns u cursor e Hb Hne Hcur [Hacyc _]. split.
  - intros [Hout Hnot].
    destruct (Z.eq_dec e cursor) as [->| Hdiff]; [right; reflexivity | left].
    split; [exact Hout |]. intros [_ Hsuf].
    apply Hnot.
    destruct (next_chain_inv _ _ _ Hsuf) as [-> | [Hnn Hrest]];
      [contradiction | split; auto].
  - intros [[Hout Hnot] | ->].
    + split; [exact Hout |]. intros [Hnn Hsuf]. apply Hnot. split; [exact Hne |].
      apply next_chain_tail_to_head; auto.
    + split; [exact Hcur |]. intros [Hnn Hsuf].
      destruct (Z.eq_dec (Znth cursor ns (-1)) (-1)) as [Heq | Hnm].
      * rewrite Heq in Hsuf. eapply next_chain_minus_one_false; eauto.
      * apply (Hacyc cursor Hb Hnm Hsuf).
Qed.

(** ** The generic model, without a graph *)

(** [ForwardStar vok edge_count hs ns ts]: the arrays are a well-formed
    forward star over the vertices [vok] with [edge_count] edges.  What the
    edges *mean* is left to the caller: state it as
    [forall u e, outgoing hs ns u e <-> <your edge relation> u (Znth e ts 0)]
    against whatever logical object the specification already has. *)
Definition ForwardStar
    (vok : Z -> Prop) (edge_count : Z) (hs ns ts : list Z) : Prop :=
  head_values_safe vok edge_count hs /\
  edge_values_safe vok edge_count ts ns /\
  forward_star_chain_wf vok hs ns.

Lemma ForwardStar_edge_bounds :
  forall vok edge_count hs ns ts u e,
    ForwardStar vok edge_count hs ns ts ->
    vok u ->
    outgoing hs ns u e ->
    0 <= e < edge_count.
Proof.
  intros vok ec hs ns ts u e [_ [[Hts [Hns _]] _]] Hu Hout.
  apply next_chain_target_bounds in Hout. lia.
Qed.

Lemma ForwardStar_far_endpoint :
  forall vok edge_count hs ns ts u e,
    ForwardStar vok edge_count hs ns ts ->
    vok u ->
    outgoing hs ns u e ->
    vok (Znth e ts 0).
Proof.
  intros vok ec hs ns ts u e HFS Hu Hout.
  pose proof (ForwardStar_edge_bounds _ _ _ _ _ _ _ HFS Hu Hout) as Hb.
  destruct HFS as [_ [[_ [_ Hsafe]] _]]. apply Hsafe; lia.
Qed.

(** An empty head means the vertex owns nothing. *)
Lemma outgoing_head_empty :
  forall hs ns u e, Znth u hs (-1) = -1 -> ~ outgoing hs ns u e.
Proof.
  intros hs ns u e Hh Hout. unfold outgoing in Hout. rewrite Hh in Hout.
  eapply next_chain_minus_one_false; eauto.
Qed.
