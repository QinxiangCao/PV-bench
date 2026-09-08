Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From SumLib Require Import Sum ZRange.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import naive_C_Rules.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From FP Require Import SetsFixedpoints PartialOrder_Setoid BourbakiWitt.
From GraphLib Require Import graph_basic reachable_basic.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrLoop
                               MonadErrHoarePartial monadesafe_lib.
Require Import PVbench.Algorithms.kosaraju.rocq.kosaraju_model_lib
  PVbench.Algorithms.kosaraju.rocq.scc_lib
  PVbench.Algorithms.kosaraju.rocq.kosaraju_refinement_lib.
Export MonadNotation.
Local Open Scope monad.

(* Re-import GraphLib's reachable_basic AFTER the MonadErr imports so that the
   graph step (G -> V -> V -> Prop) stays in scope; MonadErrBasic's Section
   monadop also declares a `step : Type` that would otherwise shadow it. *)
From GraphLib Require Import reachable_basic.
Export MonadNotation.
Local Open Scope monad.
Local Open Scope order_scope.
(* Re-open Z_scope AFTER order_scope so that `<=`/`>=` on Z keep resolving to
   Z.le/Z.ge (order_scope defines `<=` as the Order typeclass `order_rel`,
   which would otherwise shadow Z comparisons).  Program equivalence keeps
   using the order_scope `==` notation via the type-based disambiguation. *)
Local Open Scope Z_scope.
Local Open Scope sac.

(* ================================================================= *)
(* Adjacency-list graph carrier (directed, abstract).                *)
(*   adj_fwd !! u = forward (out) neighbours of u                    *)
(*   adj_rev !! u = reversed (in) neighbours of u                    *)
(*   This is the abstract graph the Kosaraju monad reasons about.    *)
(*   The C side stores the same graph in CSR layout (adj_col +       *)
(*   adj_row); the refinement relates the CSR arrays to adj_rev.     *)
(* ================================================================= *)

Record AdjGraph := MkAdjGraph {
  adj_verts : Z;
  adj_fwd   : list (list Z);
  adj_rev   : list (list Z);
}.

Definition adj_vvalid (g : AdjGraph) (v : Z) : Prop :=
  (0 <= v < adj_verts g)%Z.

Definition adj_evalid (g : AdjGraph) (e : Z * Z) : Prop :=
  let (u, v) := e in adj_vvalid g u /\ adj_vvalid g v.

Definition adj_step_aux (g : AdjGraph) (e : Z * Z) (x y : Z) : Prop :=
  e = (x, y) /\
  adj_vvalid g x /\
  adj_vvalid g y /\
  In y (nth (Z.to_nat x) (adj_fwd g) nil).

(* gvalid: well-formed adjacency list.  The converse is guarded because
   Z.to_nat maps negative integers to zero, which is not a graph index. *)
Definition AdjGraphValid (g : AdjGraph) : Prop :=
  (Zlength (adj_fwd g) = adj_verts g)%Z /\
  (Zlength (adj_rev g) = adj_verts g)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_fwd g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_rev g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    In v (nth (Z.to_nat u) (adj_fwd g) nil) <->
    In u (nth (Z.to_nat v) (adj_rev g) nil)).

(* ================================================================= *)
(* Graph type-class instances for AdjGraph.                          *)
(* ================================================================= *)

#[export] Instance AdjGraph_graph : Graph AdjGraph Z (Z * Z) := {|
  graph_basic.vvalid   := adj_vvalid;
  graph_basic.evalid   := adj_evalid;
  graph_basic.step_aux := adj_step_aux;
|}.

#[export] Instance AdjGraph_gvalid : GValid AdjGraph := AdjGraphValid.

#[export] Instance AdjGraph_stepvalid : StepValid AdjGraph Z (Z * Z).
Proof.
  constructor; intros g e x y Hstep.
  - destruct Hstep as [_ [Hvx [_ _]]]. exact Hvx.
  - destruct Hstep as [_ [_ [Hvy _]]]. exact Hvy.
  - destruct Hstep as [Heq [Hvx [Hvy _]]]. subst e.
    unfold adj_evalid. simpl. split; assumption.
Defined.

#[export] Instance AdjGraph_stepuniquedirected : StepUniqueDirected AdjGraph Z (Z * Z).
Proof.
  constructor; intros g e x1 y1 x2 y2 _ H1 H2.
  destruct H1 as [He1 _]. destruct H2 as [He2 _].
  rewrite He1 in He2. injection He2 as Hx Hy. subst. split; reflexivity.
Defined.

#[export] Instance AdjGraph_finitegraph : FiniteGraph AdjGraph Z (Z * Z).
Proof.
  refine {| graph_basic.listV := fun g => map Z.of_nat (seq 0 (Z.to_nat (adj_verts g))) |}.
  intros g Hg v Hv. unfold adj_vvalid in Hv.
  destruct Hv as [Hv1 Hv2].
  apply in_map_iff. exists (Z.to_nat v). split.
  - lia.
  - apply in_seq. lia.
Defined.

(* ================================================================= *)
(* Concrete KosarajuGraph packaging over AdjGraph.                   *)
(* Wraps the Section-parameterised definitions into closed,          *)
(* parameter-free symbols exportable to the C side.                  *)
(* ================================================================= *)

Definition KG : KosarajuGraph AdjGraph Z (Z * Z) :=
  {| kos_graph    := AdjGraph_graph;
     kos_gvalid   := AdjGraph_gvalid;
     kos_stepvalid := AdjGraph_stepvalid;
     kos_unique   := AdjGraph_stepuniquedirected;
     kos_finite   := AdjGraph_finitegraph;
  |}.

(* The Kosaraju abstract state, closed over V = Z. *)
Definition KSt : Type := @St Z.

(* A concrete (empty) adjacency-list graph used to instantiate the
   Section-parameterised monad programs into closed, parameter-free
   symbols.  The actual graph contents live on the C heap side; this
   carrier only carries the type-level packaging. *)
Definition empty_adj : AdjGraph := {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |}.

(* ================================================================= *)
(* Closed monad program symbols, instantiating the Section-           *)
(* parameterised DFS_finish / DFS_scc over empty_adj.  These are the  *)
(* high-level (mathematical) specs the C functions refine.            *)
(*                                                                   *)
(* Continuation forms (dfs_finish_from / dfs_scc_from) and the C-side *)
(* preconditions (pre_dfs1 / pre_dfs2) are added by the annotation    *)
(* phase (annotation_scratch_lib -> integrated here once checked).    *)
(* ================================================================= *)

Definition dfs_finish (g : AdjGraph) (u : Z) : program KSt unit :=
  @DFS_finish AdjGraph Z (Z * Z) KG g u.

Definition dfs_finish_schedule (g : AdjGraph) (start fuel : Z) : program KSt unit :=
  @kosaraju_finish_schedule AdjGraph Z (Z * Z) KG g
    (fun i => Z.of_nat i) (Z.to_nat start) (Z.to_nat fuel).

Definition dfs_finish_scheduleK (g : AdjGraph) (start fuel : Z)
  (_ : unit) : program KSt unit :=
  dfs_finish_schedule g start fuel.

Definition dfs_scc (g : AdjGraph) (root u : Z) : program KSt unit :=
  @DFS_scc AdjGraph Z (Z * Z) KG g root u.

(* A case-local phase-2 scheduling bridge.  The scheduled monad program
   chooses between skipping an already visited root and running the C-shaped
   [visit2; set_scc_id; dfs_scc] iteration.  The residual program is passed
   into both branches, so the [visited2] condition is evaluated in the actual
   current state rather than being classified at [init_st]. *)
Definition phase2_c_step (g : AdjGraph) (root : Z) (k : program KSt unit)
  : program KSt unit :=
  if_else (fun st => @visited2 Z st root)
    k
    (visit2 root;; set_scc_id root root;; dfs_scc g root root;; k).

Definition phase2_c_schedule (g : AdjGraph) (root_at : nat -> Z)
           (start fuel : nat) : program KSt unit :=
  @kosaraju_scc_schedule AdjGraph Z (Z * Z) KG g root_at start fuel.

Definition applyf {A B : Type} (f : A -> B) (a : A) := f a.

(* ================================================================= *)
(* CSR layout helpers (pure mathematical).                            *)
(*   m_of row_l      = row_l[length-1] = packed neighbour count       *)
(*   csr_lo u row_l  = row_l[u]       = start offset of u's neighbours*)
(*   csr_hi u row_l  = row_l[u+1]     = end offset of u's neighbours  *)
(* ================================================================= *)

Definition m_of (row_l : list Z) : Z :=
  Znth (Zlength row_l - 1) row_l 0.

Definition csr_lo (u : Z) (row_l : list Z) : Z :=
  Znth u row_l 0.

Definition csr_hi (u : Z) (row_l : list Z) : Z :=
  Znth (u + 1) row_l 0.

Definition zrange_sum_Znth (lo hi : Z) (l : list Z) : Z :=
  Sum.sum (fun i => lo <= i < hi) (fun i => Znth i l 0).

Definition transpose_count_ready (n j : Z) (cnt_l : list Z) : Prop :=
  zrange_sum_Znth 0 n cnt_l = j /\
  (forall k, 0 <= k < n -> 0 <= Znth k cnt_l 0).

Definition transpose_prefix_inv
  (n m v sum_v : Z) (rr_l cnt_l : list Z) : Prop :=
  zrange_sum_Znth 0 n cnt_l = m /\
  sum_v = zrange_sum_Znth 0 v cnt_l /\
  (forall k, 0 <= k < n -> 0 <= Znth k cnt_l 0) /\
  (forall k, v <= k < n -> Znth k rr_l 0 = Znth k cnt_l 0).

Definition zrange_count_value (lo hi v : Z) (col_l : list Z) : Z :=
  Sum.sum (fun i => lo <= i < hi)
          (fun i => if Z.eq_dec (Znth i col_l 0) v then 1 else 0).

Definition transpose_scatter_inv
  (n m j : Z) (fadj_col_l rr_l pos_l : list Z) : Prop :=
  0 <= j <= m /\
  n <= Zlength pos_l /\
  (forall v, 0 <= v < n ->
     Znth v pos_l 0 =
       Znth v rr_l 0 + zrange_count_value 0 j v fadj_col_l) /\
  (forall v, 0 <= v < n ->
     0 <= Znth v rr_l 0 /\
     Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l <= m).

Definition transpose_scatter_rows
  (n m : Z) (fadj_col_l rr_l : list Z) : Prop :=
  Zlength rr_l = n + 1 /\
  m_of rr_l = m /\
  (forall v, 0 <= v < n ->
     csr_hi v rr_l =
       Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l) /\
  (forall a b, 0 <= a < n -> 0 <= b < n -> a < b ->
     csr_hi a rr_l <= csr_lo b rr_l).

Definition transpose_scatter_contents
  (g : AdjGraph) (n j : Z)
  (fadj_row_l fadj_col_l rr_l rc_l : list Z) : Prop :=
  (forall dst p, 0 <= dst < n ->
     csr_lo dst rr_l <= p <
       Znth dst rr_l 0 + zrange_count_value 0 j dst fadj_col_l ->
     0 <= Znth p rc_l 0 < n) /\
  (forall dst src, 0 <= dst < n -> 0 <= src < n ->
     ((exists p,
         csr_lo dst rr_l <= p <
           Znth dst rr_l 0 + zrange_count_value 0 j dst fadj_col_l /\
         Znth p rc_l 0 = src) <->
      (exists t,
         0 <= t < j /\
         csr_lo src fadj_row_l <= t < csr_hi src fadj_row_l /\
         Znth t fadj_col_l 0 = dst))).

Definition transpose_count_values
  (n j : Z) (fadj_col_l cnt_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    Znth v cnt_l 0 = zrange_count_value 0 j v fadj_col_l.

Definition transpose_prefix_offsets
  (n v : Z) (rr_l pos_l cnt_l : list Z) : Prop :=
  n <= Zlength rr_l /\
  n <= Zlength pos_l /\
  (forall k, 0 <= k < v ->
     Znth k rr_l 0 = zrange_sum_Znth 0 k cnt_l /\
     Znth k pos_l 0 = zrange_sum_Znth 0 k cnt_l) /\
  (forall k, v <= k < n ->
     Znth k rr_l 0 = Znth k cnt_l 0).

(* ================================================================= *)
(* Scoped abstract-state preconditions.                              *)
(*                                                                   *)
(* pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st :        *)
(*   relates the abstract monad state st to the CSR arrays the C     *)
(*   side owns.  vis1/fin/timer are encoded as Z lists over the      *)
(*   abstract St fields (visited1 as 0/1, finish as nat-to-Z, timer  *)
(*   nat).  Pure mathematical relation; NOT an algorithm mirror.     *)
(*                                                                   *)
(* pre_dfs2 is the phase-2 analogue over the forward graph; it also  *)
(* carries the SCC-id array sid_l.                                   *)
(* ================================================================= *)

(* ================================================================= *)
(* count_nonzero: number of nonzero entries in a Z list.             *)
(*   The C side encodes "visited" as 0/1 in vis1/vis2, so            *)
(*   count_nonzero vis_l = number of visited vertices.               *)
(*   The abstract DFS always visit1's a vertex BEFORE set_finish'ing *)
(*   it, hence timer <= count_nonzero vis, i.e. the difference       *)
(*   count_nonzero vis - timer = #visited-but-not-finished, which    *)
(*   dfs1 preserves.  This is the maintainable bound on the timer;   *)
(*   a bare `timer < n` is NOT maintainable through recursion.       *)
(* ================================================================= *)
Fixpoint count_nonzero (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | z :: rest => (if Z.eqb z 0 then 0%Z else 1%Z) + count_nonzero rest
  end.

(* Replacing position u with a nonzero value v increases count_nonzero by
   exactly 1 iff the old entry at u was zero; otherwise it is unchanged.
   Requires u to be in range [0, Zlength l). *)

(* Specialisation: replacing a zero entry by 1 increases count by 1. *)

(* Reading back a list after a positional write.  Generic, pure-list;       *)
(* used by the dfs2 Inv establishment/preservation (sid/vis after the       *)
(* preamble's vis[u]=1; sid[u]=sid[root], and the recurse-call poststate).  *)

(* Pure C-side well-formedness of the CSR/graph input (no monad state).
   These describe the input arrays and the abstract graph; they belong in
   the C function's Require, NOT inside the safeExec precondition. *)
Definition csr_wf1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength radj_row_l = adj_verts g + 1 /\
  Zlength vis1_l = adj_verts g /\
  Zlength fin_l = adj_verts g /\
  m_of radj_row_l = Zlength radj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u radj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u radj_row_l <= m_of radj_row_l)%Z /\
  (* every packed neighbour entry is a valid vertex id in [0, adj_verts g) *)
  (forall j, (0 <= j < m_of radj_row_l)%Z ->
     (0 <= Znth j radj_col_l 0 < adj_verts g)%Z) /\
  (* CSR row array is non-decreasing: each vertex's neighbour range is valid *)
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u radj_row_l <= csr_hi u radj_row_l)%Z) /\
  (m_of radj_row_l <= 2147483646)%Z.

Definition radj_col_particular (g: AdjGraph) (radj_col_l: list Z) : Prop :=
  forall j, (0 <= j < Zlength radj_col_l)%Z ->
     (0 <= Znth j radj_col_l 0 < adj_verts g)%Z.

(* CSR faithfulness: the packed CSR neighbour arrays list exactly the       *)
(* abstract graph's out-/in-neighbours.  This is the refinement link        *)
(* between the C cursor (a CSR position sweep) and the abstract monad's     *)
(* `step_aux g e u v` nondeterministic choice.  It is a pure mathematical   *)
(* property of the (immutable) graph + CSR arrays, so it is loop-invariant  *)
(* in the C code and cheap to carry through dfs1/dfs2.                      *)
Definition csr2_faithful (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) : Prop :=
  forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    step g u v <->
    exists j, (csr_lo u fadj_row_l <= j < csr_hi u fadj_row_l)%Z /\ Znth j fadj_col_l 0 = v.

Definition csr1_faithful (g: AdjGraph) (radj_col_l radj_row_l: list Z) : Prop :=
  forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    step g v u <->
    exists j, (csr_lo u radj_row_l <= j < csr_hi u radj_row_l)%Z /\ Znth j radj_col_l 0 = v.

(* pre_dfs1: ONLY the C-program-state <-> monad-state correspondence. *)
Definition pre_dfs1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z)
  (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited1 st u <-> Znth u vis1_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     finish st u = Z.to_nat (Znth u fin_l 0)) /\
  timer st = Z.to_nat timer_v /\
  (forall u, ~ (0 <= u < adj_verts g)%Z -> ~ visited1 st u) /\
  (forall u, ~ (0 <= u < adj_verts g)%Z -> finish st u = 0%nat).

(* The C program stores finished vertices by completion position:
   [fin_l[t] = v] means that the monadic finish time of [v] is [t + 1].
   Only [0, timer_v) is initialized; the remaining malloc'ed suffix is
   deliberately unconstrained.  This is the refinement relation used by the
   current C proof.  [pre_dfs1] is retained as a legacy compatibility layer
   for older helper lemmas, but is no longer used by the C contracts. *)
Definition fin_sequence_rep (g : AdjGraph) (fin_l : list Z)
  (timer_v : Z) (st : KSt) : Prop :=
  (0 <= timer_v <= adj_verts g)%Z /\
  Zlength fin_l = adj_verts g /\
  timer st = Z.to_nat timer_v /\
  (forall t, (0 <= t < timer_v)%Z ->
     (0 <= Znth t fin_l 0 < adj_verts g)%Z /\
     finish st (Znth t fin_l 0) = S (Z.to_nat t)) /\
  (forall v, (0 <= v < adj_verts g)%Z ->
     finish st v <> 0%nat ->
     exists t, (0 <= t < timer_v)%Z /\ Znth t fin_l 0 = v) /\
  (forall v, ~ (0 <= v < adj_verts g)%Z -> finish st v = 0%nat).

Definition pre_dfs1_sequence (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z)
  (st : KSt) : Prop :=
  (forall v, (0 <= v < adj_verts g)%Z ->
     visited1 st v <-> Znth v vis1_l 0 <> 0%Z) /\
  (forall v, ~ (0 <= v < adj_verts g)%Z -> ~ visited1 st v) /\
  fin_sequence_rep g fin_l timer_v st.

(* Compatibility name for older proof-side helpers.  Cursor refinements must
   not strengthen the concrete C-array/monad-state representation with the
   transient algorithm fact that an active root has not yet finished. *)
Definition pre_dfs1_active_sequence (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v root : Z)
  (st : KSt) : Prop :=
  pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v st.

Definition pre_dfs1_sequence_initial (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (n : Z)
  (st : KSt) : Prop :=
  st = @Kosaraju.init_st Z /\
  pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l 0 st /\
  Zlength vis1_l = n /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 = 0%Z).

Definition dfs1_sequence_state_ready (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z) : Prop :=
  csr_wf1 g radj_col_l radj_row_l vis1_l fin_l /\
  csr1_faithful g radj_col_l radj_row_l /\
  (0 <= timer_v <= adj_verts g)%Z.

Definition dfs1_sequence_extension (g : AdjGraph)
  (vis0 fin0 : list Z) (timer0 : Z)
  (vis1 fin1 : list Z) (timer1 root : Z) : Prop :=
  (0 <= timer0 /\ timer0 <= timer1 /\ timer1 <= adj_verts g)%Z /\
  (forall v, (0 <= v < adj_verts g)%Z ->
     Znth v vis0 0 <> 0%Z -> Znth v vis1 0 <> 0%Z) /\
  Znth root vis1 0 <> 0%Z /\
  (forall t, (0 <= t < timer0)%Z -> Znth t fin1 0 = Znth t fin0 0) /\
  (forall v, (0 <= v < adj_verts g)%Z ->
     Znth v vis0 0 <> 0%Z ->
     forall t, (timer0 <= t < timer1)%Z -> Znth t fin1 0 <> v).

Definition dfs1_finish_prefix_marked
    (fin_l vis_l : list Z) (timer_v n : Z) : Prop :=
  forall t, (0 <= t < timer_v)%Z ->
    (0 <= Znth t fin_l 0 < n)%Z /\
    Znth (Znth t fin_l 0) vis_l 0 <> 0%Z.

Definition dfs1_root_not_in_finish_prefix
    (fin_l : list Z) (timer_v root : Z) : Prop :=
  forall t, (0 <= t < timer_v)%Z -> Znth t fin_l 0 <> root.

Definition dfs1_active_sequence_extension (g : AdjGraph)
  (vis0 fin0 : list Z) (timer0 : Z)
  (vis1 fin1 : list Z) (timer1 root : Z) : Prop :=
  dfs1_sequence_extension g vis0 fin0 timer0 vis1 fin1 timer1 root /\
  dfs1_root_not_in_finish_prefix fin1 timer1 root.

Definition phase1_sequence_refinement (g : AdjGraph)
  (radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l : list Z)
  (timer_v n u : Z) : Prop :=
  dfs1_sequence_state_ready g radj_col_l radj_row_l vis_l fin_l timer_v /\
  (timer_v <= count_nonzero vis_l)%Z /\
  safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis_l fin_l timer_v)
    (dfs_finish_schedule g u (n - u))
    (result_state
      (pre_dfs1_sequence_initial g radj_col_l radj_row_l vis0_l fin0_l n)
      (dfs_finish_schedule g 0 n)).

Definition phase2_sequence_state_rep
    (g : AdjGraph) (fin_l vis1_l vis2_l sid_l : list Z)
    (timer_v n : Z) (st : KSt) : Prop :=
  pre_dfs1_sequence g nil nil vis1_l fin_l timer_v st /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 <> 0%Z) /\
  (forall v, (0 <= v < n)%Z ->
     visited2 st v <-> Znth v vis2_l 0 <> 0%Z) /\
  (forall v, (0 <= v < n)%Z -> visited2 st v ->
     Z.of_nat (scc_id st v) = Znth v sid_l 0).

Definition phase2_sequence_final_post
    (g : AdjGraph) (_ : unit) (st : KSt) : Prop :=
  (forall v, (0 <= v < adj_verts g)%Z -> visited2 st v) /\
  (forall u v,
    (0 <= u < adj_verts g)%Z ->
    (0 <= v < adj_verts g)%Z ->
    (scc_id st u = scc_id st v <->
     @Kosaraju.mutually_reachable AdjGraph Z (Z * Z) KG g u v)).

Definition pre_dfs1_initial (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (n : Z)
  (st : KSt) : Prop :=
  st = @Kosaraju.init_st Z /\
  pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l 0 st /\
  (forall u, (0 <= u < n)%Z ->
     Znth u vis1_l 0 = 0%Z /\ Znth u fin_l 0 = 0%Z).

Definition dfs1_finish_arrays_inv (g : AdjGraph)
  (vis1_l fin_l : list Z) (timer_v : Z) : Prop :=
  (0 <= timer_v)%Z /\
  timer_v = count_nonzero fin_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     Znth u vis1_l 0 = 0%Z ->
     Znth u fin_l 0 = 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     Znth u vis1_l 0 <> 0%Z ->
     (0 <= Znth u fin_l 0 <= timer_v)%Z).

(* DFS1 phase-1 readiness is intentionally separate from [pre_dfs1].
   [pre_dfs1] remains the C-array/monad-state correspondence.  The state
   predicate is preserved by a DFS1 call; the call predicate adds the root
   facts needed to apply [DFS_finish_phase1_plus]. *)
Definition dfs1_phase1_state_ready (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z) : Prop :=
  csr_wf1 g radj_col_l radj_row_l vis1_l fin_l /\
  csr1_faithful g radj_col_l radj_row_l /\
  dfs1_finish_arrays_inv g vis1_l fin_l timer_v.

Definition fin_order_prefix
    (fin_l vis_l : list Z) (timer n : Z) : Prop :=
  0 <= timer <= n /\
  Zlength fin_l = n /\
  Zlength vis_l = n /\
  (forall i, 0 <= i < timer -> 0 <= Znth i fin_l 0 < n) /\
  (forall i, timer <= i < n -> Znth i fin_l 0 = 0) /\
  (forall v, 0 <= v < n ->
    (Znth v vis_l 0 <> 0 <->
      exists i, 0 <= i < timer /\ Znth i fin_l 0 = v)).

Definition dfs1_phase1_ready (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v u : Z) : Prop :=
  dfs1_phase1_state_ready g radj_col_l radj_row_l vis1_l fin_l timer_v /\
  (0 <= u < adj_verts g)%Z /\
  Znth u vis1_l 0 = 0%Z /\
  (forall st,
    pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st ->
    ~ @visited1 Z st u /\
    @vvalid AdjGraph Z (Z * Z)
      (@kos_graph AdjGraph Z (Z * Z) KG) g u) /\
  fin_order_prefix fin_l vis1_l timer_v (adj_verts g).

Definition pre_dfs1_phase1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v u : Z)
  (st : KSt) : Prop :=
  pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st /\
  dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u.

Definition dfs1_phase1_result (g : AdjGraph) (u : Z)
  (entry : KSt) (st : KSt) : Prop :=
  @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
  @visited1 Z st u /\
  @visited1 Z entry ⊆ @visited1 Z st /\
  (forall x, @visited1 Z entry x ->
     @finish Z st x = @finish Z entry x).

Definition dfs_finish_phase1_checked (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v u : Z)
  : program KSt unit :=
  entry <- get (fun st entry => entry = st);;
  assertS (fun st =>
    st = entry /\
    pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u st);;
  dfs_finish g u;;
  assertS (dfs1_phase1_result g u entry).

Definition csr_wf2 (g : AdjGraph)
  (fadj_col_l fadj_row_l vis2_l sid_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength fadj_row_l = adj_verts g + 1 /\
  Zlength vis2_l = adj_verts g /\
  Zlength sid_l = adj_verts g /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u fadj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u fadj_row_l <= m_of fadj_row_l)%Z /\
  (* every packed neighbour entry is a valid vertex id in [0, adj_verts g) *)
  (forall j, (0 <= j < m_of fadj_row_l)%Z ->
     (0 <= Znth j fadj_col_l 0 < adj_verts g)%Z) /\
  (* CSR row array is non-decreasing: each vertex's neighbour range is valid *)
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u fadj_row_l <= csr_hi u fadj_row_l)%Z) /\
  (m_of fadj_row_l <= 2147483646)%Z.

(* The immutable forward-CSR part of [csr_wf2].  It deliberately omits
   vis2/sid: those lists are mutable phase-2 work arrays, while every
   conjunct below is fixed by the CSR construction before [kosaraju]. *)
Definition csr_wf2_core (g : AdjGraph)
  (fadj_col_l fadj_row_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength fadj_row_l = adj_verts g + 1 /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u fadj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u fadj_row_l <= m_of fadj_row_l)%Z /\
  (forall j, (0 <= j < m_of fadj_row_l)%Z ->
     (0 <= Znth j fadj_col_l 0 < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u fadj_row_l <= csr_hi u fadj_row_l)%Z) /\
  (m_of fadj_row_l <= 2147483646)%Z.

(* pre_dfs2: ONLY the C-program-state <-> monad-state correspondence. *)
Definition pre_dfs2 (g : AdjGraph)
  (fadj_col_l fadj_row_l vis2_l sid_l : list Z) (root_v : Z)
  (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited2 st u <-> Znth u vis2_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     scc_id st u = Z.to_nat (Znth u sid_l 0)).

(* The MonadErr model supplies [DFS_scc_absorb]: when a vertex and all of its
   forward neighbours are already marked, and its SCC label agrees with the
   root label, the recursive call has a no-op normal transition.  The C
   refinement uses the following two local bridges to turn that transition
   into the residual [safeExec] return obligation. *)

(* ================================================================= *)
(* Loop continuations — cursor-parameterised.                        *)
(*                                                                   *)
(* The abstract DFS_finish u / DFS_scc root u are non-deterministic  *)
(* over (e,v) ∈ E×V.  The C side reifies this choice as a CSR cursor  *)
(* sweep over u's reverse (resp. forward) neighbours: at cursor i    *)
(* the chosen vertex is radj_col_l[i] (resp. fadj_col_l[i]).         *)
(*                                                                   *)
(* dfs_finish_iter g radj_col_l u hi i fuel is a structurally        *)
(* decreasing (fuel) cursor sweep starting at i.  At each step v =   *)
(* radj_col_l[i]; if v is already visited1, SKIP (advance cursor);   *)
(* otherwise RECURSE into dfs_finish g v then advance.  Once the     *)
(* cursor reaches hi (i >= hi) it performs the set_finish u timer    *)
(* tail — mirroring the C post-loop {t0=timer; fin[u]=t0+1; timer++} *)
(* and the DFS_finish_f break branch's `get timer ;; set_finish u t`. *)
(*                                                                   *)
(* dfs_scc_iter is the phase-2 analogue over the forward graph; its  *)
(* exit is `ret tt` because dfs2 has NO post-loop block (the         *)
(* function returns immediately after the cursor sweep).             *)
(*                                                                   *)
(* dfs_finish_from / dfs_scc_from specialise iter with fuel          *)
(* (csr_hi u row_l - i), so the entry (i = csr_lo u), step, and      *)
(* exit (i = csr_hi u) unfoldings discharge by Fixpoint computation. *)
(* This block uses only proved local facts.                          *)
(* ================================================================= *)

(* AdjGraph VListBijective instance: derived from FiniteGraph, matching the
   Section-local `kos_vlist` in Kosaraju.v.  This lets `bijective_listV g`
   resolve in lib.v definitions (needed by dfs_finish_repeat_body's assertS
   timer <= |V|), and keeps definitional equality with DFS_finish_f's body. *)
#[export] Instance AdjGraph_vlistbijective : VListBijective AdjGraph Z (Z * Z) :=
  finite_graph_vlist_bijective AdjGraph Z (Z * Z).

Fixpoint dfs_finish_iter
  (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
          assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t)
  | S fuel' =>
      if Z.leb hi i then assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
                           assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t
      else
        (* vis-conditional cursor — matches the C `if (vis1[v]==0)` and the
           abstract repeat_break's `assume ~visited1 st v` guard.  At position
           i, v = Znth i radj_col_l 0: if v is already visited1, SKIP (advance
           cursor); otherwise RECURSE into dfs_finish g v then advance. *)
        if_else (fun st => visited1 st (Znth i radj_col_l 0))
                (dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
                (pre <- get (fun st pre => pre = st);;
                 _ <- dfs_finish g (Znth i radj_col_l 0) ;;
                 assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                                        visited1 st (Znth i radj_col_l 0) /\
                                        visited1 pre ⊆ visited1 st);;
                 dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
  end.

Fixpoint dfs_scc_iter
  (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      if Z.leb hi i then ret tt
      else
        (* B1: vis-conditional cursor — matches the C `if (vis2[v]==0)` and the
           abstract repeat_break's `assume ~visited2 st v` guard.  At position
           i, v = Znth i fadj_col_l 0: if v is already visited2, SKIP (advance
           cursor); otherwise RECURSE into dfs_scc root v then advance. *)
        if_else (fun st => visited2 st (Znth i fadj_col_l 0))
                (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel')
                (_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
                 dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel')
  end.

Definition dfs_finish_from
  (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z) : program KSt unit :=
  dfs_finish_iter g radj_col_l u (csr_hi u radj_row_l) i
    (Z.to_nat (csr_hi u radj_row_l - i)).

Definition dfs_scc_from
  (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z) : program KSt unit :=
  dfs_scc_iter g fadj_col_l root u (csr_hi u fadj_row_l) i
    (Z.to_nat (csr_hi u fadj_row_l - i)).

Definition dfs_finish_fromK
  (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z) : unit -> program KSt unit :=
  fun _ => dfs_finish_from g radj_col_l radj_row_l u i.

Definition dfs_scc_fromK
  (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z) : unit -> program KSt unit :=
  fun _ => dfs_scc_from g fadj_col_l fadj_row_l root u i.

(* ================================================================= *)
(* Structural unfolding lemmas for the cursor continuations.          *)
(*                                                                   *)
(* These discharge by Fixpoint computation; they expose the cursor    *)
(* step (recurse into the chosen neighbour, continue at i+1) and the  *)
(* exit (cursor exhausted: re-enter dfs_finish / dfs_scc to run the   *)
(* abstract set_finish / finalisation tail).                          *)
(* ================================================================= *)

(* Under MonadErr, `program Σ A` is a record {nrm; err}.  dfs_scc (hence
   dfs_scc_iter / dfs_scc_from, which are built only from dfs_scc, if_else,
   choice, test, and bind) never raises an error: every construct used has an
   empty err component (dfs_scc_f's body uses assume, not assert/assertS; the
   custom visit2/set_scc_id have err := ∅).  We never need to prove the
   full no-error fact by induction over BW_fix iterations, because the
   safeExec-based skip/recurse closers only need an err IMPLICATION
   (err-at-i+1 -> err-at-i) under the visited/¬visited cursor hypothesis,
   which follows by one-level unfolding of the if_else/choice/bind err
   structure (using bind_err_iff / bind_nrm_iff from MonadErrBasic). *)

(* The dfs_finish_from / dfs_scc_from level lemmas, accounting for the
   Z.to_nat fuel accounting.  When i < hi, Z.to_nat (hi - i) = S _ and
   the next cursor's fuel is Z.to_nat (hi - (i+1)) = pred (Z.to_nat (hi-i)). *)

(* Reverse-direction err-imps (err at i -> err at i+1 / bind), used by the
   repeat_break-to-cursor simulation dfs_scc_from_sim.  The forward err-imps
   above go i+1 -> i (matching dfs2_skip_close / dfs2_recurse_close); the
   simulation peels the cursor step FORWARD (i -> i+1), so it needs the
   reverse direction, which holds under the same visited/~visited hypothesis
   (the failing test branch contributes no err at st). *)

(* dfs2_return_close (the Gap-A loop-exit closer) was HERE; it depended on   *)
(* the absorb chain (dfs_scc_safe_return) and is deleted alongside it — see   *)
(* the SEMANTIC GAP note near the former dfs_scc_absorb.                       *)

(* Absorb chain REMOVED.  With the cursor exit set to `ret tt` (dfs2) and
   `get timer ;; set_finish u t` (dfs1), the loop-exit VC no longer needs to
   bridge a re-entered `dfs_scc g root u` / `dfs_finish g u` to a no-op or
   set_finish transition via DFS_scc_absorb.  The exit lemma
   (dfs_scc_from_exit / dfs_finish_from_exit) now equates the cursor
   continuation directly to the exit monad, so the return VC is a plain
   safeExec_proequiv.  No unproved absorb lemmas are needed. *)

(* dfs2 Gap A (loop exit) closer: at i >= hi, dfs_scc_from ... u i == ret tt,
   so `safeExec P (dfs_scc_from ... u i) X` is rewritten to
   `safeExec P (ret tt) X` by program equivalence.  Trivial. *)

(* dfs1 loop-exit closer: at i >= hi, dfs_finish_from ... u i ==
   (t <- get timer ;; set_finish u t).  The C post-loop reads timer_p[0],
   sets fin[u] = t0+1, timer_p[0] = t0+1 — exactly the nrm transition of
   `get (fun st t => t = timer st) ;; set_finish u t`: from st (timer = timer_m)
   it steps to st' with timer st' = S (timer st) and finish st' u = S (timer st).
   Given the safeExec witness sigma with pre_dfs1 vis_m fin_m timer_m and
   timer_m = Z.to_nat (timer sigma), the post-state sigma' has
     timer sigma' = S timer_m,  finish sigma' u = S timer_m,
   which matches pre_dfs1 vis_m (replace_Znth u (timer_m+1) fin_m) (S timer_m)
   (vis1 unchanged by set_finish; finish[u] = timer_m+1; other finish preserved).
   Then X tt sigma' follows from the wp of the exit monad. *)

(* B1 fallouts: conditional step-closers for the recurse VC (partial_solve_8)
   and the Gap-B skip VC.  Each extracts the safeExec witness sigma, derives
   visited2/~visited2 of v (= Znth i fadj_col_l 0) at sigma via pre_dfs2, applies
   dfs_scc_from_skip_step / dfs_scc_from_recurse_step, and reconstructs. *)

(* dfs1 analogues of dfs2_skip_close / dfs2_recurse_close.  vis-conditional
   cursor: at position i, v = Znth i radj_col_l 0; if visited1, SKIP (advance
   cursor); if not, RECURSE into dfs_finish g v then advance.  Each extracts
   the safeExec witness sigma, derives visited1/~visited1 of v at sigma via
   pre_dfs1, applies dfs_finish_from_skip_step / dfs_finish_from_recurse_step,
   and reconstructs. *)

(* Scanned-neighbours conjunct helper (dfs2_entail_wit_3 group).  At cursor i,
   vertex v = Znth i fadj_col_l 0.  The conjunct requires both the lo-end
   neighbour and the i-end (= v) neighbour to be visited2.  The i-end is just
   v's visited fact (Hvisv); the lo-end is the scanned range [lo, i) when lo < i,
   or reduces to v when lo = i (the range is then empty and Znth lo = v).  This
   encapsulates the lo=i case split so the main-VC dispatch need not key on
   PreH numbers (reorder-immune). *)

(* ===================================================================== *)
(* dfs2_entry_close infrastructure (phase-2 entry refinement).            *)
(*                                                                        *)
(* The entry VC (dfs2_entail_wit_1_split_goal_9) reduces to: given        *)
(*   safeExec (pre_dfs2 vis sid) (dfs_scc g root u) X,                    *)
(* show safeExec (pre_dfs2 vis1 sid') (dfs_scc_from g fc fr root u lo) X, *)
(* where vis1 = replace_Znth u 1 vis, sid' = replace_Znth u (sid[root]) sid. *)
(*                                                                        *)
(* dfs2_repeat_body is the body of DFS_scc_f, u-parametrised, with the    *)
(* recursive leaf W = dfs_scc g root.  It is definitionally equal to the  *)
(* body of DFS_scc_f g root (dfs_scc g root) u (verified by reflexivity    *)
(* in dfs2_scc_unfold_repeat), so repeat_break congruence is free.        *)
(*                                                                        *)
(* visit2_pre_dfs2_step / set_scc_id_pre_dfs2_step peel the visit2 u +    *)
(* set_scc_id u root prelude off safeExec(dfs_scc g root u), leaving      *)
(* safeExec over repeat_break (dfs2_repeat_body g root u) empty at the    *)
(* post-visit/set_scc_id state.  dfs2_visit_setid_decompose composes the  *)
(* two peels with dfs2_scc_unfold_repeat + safeExec_proequiv.             *)
(*                                                                        *)
(* The remaining piece is dfs_scc_from_sim: the cursor-vs-repeat_break    *)
(* simulation (safe(repeat_break B e_set_i) -> safe(dfs_scc_from ... u i)),*)
(* which is the main wp-induction workload and is tracked separately.     *)
(* ===================================================================== *)

Definition dfs2_repeat_body (g: AdjGraph) (root u: Z)
  : (Z * Z -> Prop) -> program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  fun e_set =>
    choice
      (e <- any (Z * Z);;
       v <- any Z;;
       assume (fun (_ : KSt) => ~ e ∈ e_set);;
       assume (fun st => ~ visited2 st v);;
       assume (fun (_ : KSt) => step_aux g e u v);;
       dfs_scc g root v;;
       continue (e_set ∪ Sets.singleton e))
      (assume (fun st =>
                 forall (e: Z * Z) (v: Z),
                   step_aux g e u v ->
                   e ∈ e_set \/ visited2 st v);;
       assertS (fun st => scc_id st u = scc_id st root);;
       break tt).

(* ================================================================= *)
(* Reusable MonadErr helper lemmas (pure monad, no algorithm props). *)
(* Used by dfs_scc_from_sim to factor the repeat_break nrm-step out of *)
(* the simulation's BASE/RECURSE cases.                               *)
(* ================================================================= *)

(* wp_seq: sequence-specialised wp_bind, bridging the eta gap between
   `f ;; rest` (= bind f (fun _ => rest)) and wp_bind's `x <- f ;; g x`. *)

(* repeat_break_break_step: body produces by_break b at sigma (no state change)
   -> repeat_break produces b at sigma (first iteration takes the break branch). *)

(* repeat_break_break_step_gen: generalised break-step allowing the body to
   change the state (sigma -> sigma') before emitting by_break b.  Needed by
   dfs_finish_from_sim BASE: DFS_finish_f's break branch runs `set_finish u t`,
   which mutates the state, unlike phase-2's break (assertS sid ;; break). *)

(* repeat_break_continue_step: body produces by_continue a' at (σ -> σ'),
   then repeat_break body a' produces b at (σ' -> σ'') -> repeat_break body a
   produces b at (σ -> σ''). *)

(* ===================================================================== *)
(* dfs_scc_from_sim: cursor (dfs_scc_from) vs repeat_break simulation.   *)
(* The recursive dfs_scc g root v call is treated as an atom; only the   *)
(* scheduling layer (cursor vs repeat_break body dispatch) is related.   *)
(* Fuel: induction on Z.to_nat (hi - i).                                 *)
(* ===================================================================== *)

(* ===================================================================== *)
(* dfs2_entry_close: the entry refinement (split_goal_9).                *)
(* Combines dfs2_visit_setid_decompose (peel visit2 + set_scc_id prelude,*)
(* landing safeExec over repeat_break (dfs2_repeat_body g root u) ∅)     *)
(* with dfs_scc_from_sim (cursor ≡ repeat_break simulation at i=lo).     *)
(* ===================================================================== *)

(* ===================================================================== *)
(* dfs1_entry_close infrastructure (phase-1 entry refinement).           *)
(*                                                                        *)
(* The entry VC (dfs1_entail_wit_1, second disjunct) reduces to: given    *)
(*   safeExec (pre_dfs1 vis1 fin timer_v) (dfs_finish g u) X,             *)
(* show safeExec (pre_dfs1 (replace_Znth u 1 vis1) fin timer_v)           *)
(*        (dfs_finish_from g radj_col radj_row u lo) X.                   *)
(*                                                                        *)
(* dfs_finish_repeat_body is the body of DFS_finish_f, u-parametrised,    *)
(* with W = dfs_finish g.  Note: step_aux g e v u (REVERSED — u is the   *)
(* target on the reverse graph), and the break branch does `assertS      *)
(* timer = finished-count;; get timer;; set_finish u t` (state-changing, unlike *)
(* phase-2's assertS sid ;; break).                                       *)
(* ===================================================================== *)

Definition dfs_finish_repeat_body (g: AdjGraph) (u: Z)
  : (Z * Z -> Prop) -> program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  fun e_set =>
    choice
      (e <- any (Z * Z);;
       v <- any Z;;
       assume (fun (_ : KSt) => ~ e ∈ e_set);;
       assume (fun st => ~ visited1 st v);;
       assume (fun (_ : KSt) => step_aux g e v u);;
       pre <- get (fun st pre => pre = st);;
       dfs_finish g v;;
       assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                              visited1 st v /\ visited1 pre ⊆ visited1 st);;
       continue (e_set ∪ Sets.singleton e))
      (assume (fun st =>
                 forall (e: Z * Z) (v: Z),
                   step_aux g e v u ->
                   e ∈ e_set \/ visited1 st v);;
       assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
       assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));;
       t <- get (fun st t => t = timer st);;
       set_finish u t;;
       break tt).

(* visit1_pre_dfs1_step: peel the visit1 u prelude off safeExec(dfs_finish g u).
   visit1 u adds u to visited1 (visited1 st2 == visited1 st1 ∪ {u}), all other
   fields unchanged.  So pre_dfs1 vis1 fin timer_v -@ visit1 u -⥅
   pre_dfs1 (replace_Znth u 1 vis1) fin timer_v. *)

(* dfs1_visit_decompose: peel visit1 u prelude, landing safeExec over
   repeat_break (dfs_finish_repeat_body g u) ∅ at the post-visit1 state. *)

(* ===================================================================== *)
(* Reverse-direction err-imps for dfs_finish_iter / dfs_finish_from       *)
(* (phase-1 analogues of dfs_scc_iter/from_*_err_rev_imp).               *)
(* Used by dfs_finish_from_sim to peel the cursor step FORWARD (i -> i+1).*)
(* ===================================================================== *)

(* dfs_finish_repeat_body_err_from_assertS: if the break-branch closure holds
   at σ and the DFS-finish invariant assertion is false, then the repeat_break
   body errs at σ.  Used by dfs_finish_from_sim BASE to extract the asserted
   invariant from the no-err conjunct of safe σ (repeat_break B e_set) X. *)

(* ===================================================================== *)
(* dfs_finish_from_sim: cursor (dfs_finish_from) vs repeat_break          *)
(* simulation (phase-1 entry refinement core).                           *)
(*                                                                        *)
(* Differences from dfs_scc_from_sim (phase-2):                           *)
(* - csr1_faithful: step g v u <-> exists j in [lo u, hi u) with          *)
(*   Znth j radj_col 0 = v (REVERSE graph; u is the target).              *)
(* - break branch (R): assertS timer<=|V| ;; get timer ;; set_finish u t *)
(*   (state-CHANGING: timer++, finish[u]=t).  BASE case lands at sigma'   *)
(*   (= set_finish post-state), not sigma.                                *)
(* - the recursive branch now obtains DFSFinishInv, the recursive target  *)
(*   visit fact, and visited1 monotonicity from the monad-side assertS.   *)
(* - the break branch obtains DFSFinishInv and timer = finished-count     *)
(*   from the strengthened monad-side assertS before set_finish.          *)
(* ===================================================================== *)

(* ===================================================================== *)
(* dfs1_entry_close + count_pred-count_nonzero bridge.                    *)
(*                                                                        *)
(* dfs1_entry_close composes dfs1_visit_decompose (peel visit1 prelude)   *)
(* with dfs_finish_from_sim at (i = csr_lo u, e_set = empty).  The sim    *)
(* premises HcardV (count_pred(visited1 st)(bijective_listV g) >= timer)  *)
(* and Htimerbd (timer <= length(bijective_listV g)) are discharged from  *)
(* pre_dfs1 via the count_pred-count_nonzero bridge below:                *)
(*   bijective_listV g = listV g = [0,1,...,adj_verts g - 1] (NoDup+all    *)
(*     valid, so valid_NoDup_list retains all), and under pre_dfs1        *)
(*     (visited1 st v <-> Znth v vis1 0 <> 0 for 0<=v<n) the position-   *)
(*     aligned count equals count_nonzero vis1, hence >= Z.to_nat timer_v *)
(*     = timer st by PreH timer_v <= count_nonzero vis1.                  *)
(* ===================================================================== *)

(* valid_NoDup_list P l = l when l is NoDup and every element satisfies P:
   the de-dup filter keeps every element (none filtered, none duplicated). *)

(* For an AdjGraph with AdjGraphValid g, bijective_listV g is a permutation
   of the ordered vertex list [0, 1, ..., adj_verts g - 1] (= listV g):
   both are NoDup and have the same In-set (vvalid g v = 0<=v<adj_verts g),
   so NoDup_Permutation applies.  (A definitional equality is unavailable
   because the VListBijective instance is opaque.) *)

(* count_pred is invariant under Permutation (the count depends only on the
   multiset of elements, not their order). *)

(* Position-aligned count: count_pred P over [offset, offset+1, ..., offset+n-1]
   (encoded as map (fun k => offset + Z.of_nat k) (seq 0 n)) aligns positionally
   with Znth over vis1 when Zlength vis1 = Z.of_nat n and P (offset + Z.of_nat k)
   <-> Znth k vis1 0 <> 0 for 0 <= k < n.  Then the count equals
   Z.to_nat (count_nonzero vis1).  Proved by induction on n with a shifted
   offset so the tail premise closes under IH. *)

(* Bridge: count_pred (visited1 st) over bijective_listV g equals
   Z.to_nat (count_nonzero vis1), given pre_dfs1 + Zlength vis1 = adj_verts g
   + AdjGraphValid g.  Routes through the Permutation to listV (seq) and the
   position-aligned count. *)

(* Bridge the timer bound: timer st = Z.to_nat timer_v <= length (bijective_listV g).
   Uses count_nonzero_le_Zlength + Zlength vis1 = adj_verts g + the Permutation
   (length is Permutation-invariant). *)

(* ===================================================================== *)
(* dfs1_entry_close: phase-1 entry refinement (mirror of dfs2_entry_close).
   Given safeExec (pre_dfs1 vis1 fin timer_v) (dfs_finish g u) X, the
   cursor-indexed continuation dfs_finish_from g radj_col radj_row u lo
   refines dfs_finish g u at the entry cursor (i = csr_lo u radj_row_l,
   e_set = empty), under the post-visit1 precondition (vis1[u] := 1).
   Composes dfs1_visit_decompose (peel visit1 u prelude, Qed) with
   dfs_finish_from_sim (cursor vs repeat_break at i = lo, e_set = empty).
   Phase-1 invariant and timer facts are discharged inside
   dfs_finish_from_sim from the strengthened monad assertions.
   ===================================================================== *)

Definition csr_layout
  (g : AdjGraph) (col_l row_l : list Z) : Prop :=
  Zlength row_l = adj_verts g + 1 /\
  m_of row_l = Zlength col_l /\
  csr_lo 0 row_l = 0 /\
  (forall u, 0 <= u < adj_verts g ->
     0 <= csr_lo u row_l /\
     csr_lo u row_l <= csr_hi u row_l /\
     csr_hi u row_l <= m_of row_l) /\
  (forall u, 0 <= u < adj_verts g - 1 ->
     csr_hi u row_l <= csr_hi (u + 1) row_l) /\
  (forall j, 0 <= j < m_of row_l ->
     0 <= Znth j col_l 0 < adj_verts g).

Definition transpose_spec
  (g : AdjGraph) (fadj_col_l fadj_row_l radj_col_l radj_row_l : list Z)
  (n : Z) : Prop :=
  adj_verts g = n /\
  AdjGraphValid g /\
  m_of fadj_row_l = m_of radj_row_l /\
  csr2_faithful g fadj_col_l fadj_row_l /\
  csr_layout g radj_col_l radj_row_l /\
  csr1_faithful g radj_col_l radj_row_l.

Definition fin_values_in_int_range (fin_l : list Z) (n : Z) : Prop :=
  forall v, 0 <= v < n -> 0 <= Znth v fin_l 0 <= INT_MAX.

(* This is the phase-1 refinement boundary carried by the C outer loop.
   The residual program is not an implementation mirror: it relates the
   current C arrays to the one whole monadic finish schedule rooted at the
   initial C state.  At cursor [n] the residual is [ret], so its result
   state is precisely the current C array representation of Phase1_Order. *)
Definition phase1_residual_refinement (g : AdjGraph)
  (radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l : list Z)
  (timer_v n u : Z) : Prop :=
  fin_values_in_int_range fin_l n /\
  fin_order_prefix fin_l vis_l timer_v n /\
  dfs1_phase1_state_ready g radj_col_l radj_row_l vis_l fin_l timer_v /\
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis_l fin_l timer_v)
    (dfs_finish_schedule g u (n - u))
    (result_state
      (pre_dfs1_initial g radj_col_l radj_row_l vis0_l fin0_l n)
      (dfs_finish_schedule g 0 n)).

(* Sequence-valued phase-1 finish state.  Unlike the legacy finish-time
   relation above, [fin_l] stores each newly finished vertex at the next
   timer position; phase 2 consumes this sequence from right to left. *)
Definition order_init_prefix (n k : Z) (order_l : list Z) : Prop :=
  n <= Zlength order_l /\
  forall i, 0 <= i < k -> Znth i order_l 0 = i.

Definition order_entries_in_range (n : Z) (order_l : list Z) : Prop :=
  forall i, 0 <= i < n -> 0 <= Znth i order_l 0 < n.

Definition list_prefix_no_dup (n : Z) (l : list Z) : Prop :=
  forall i j,
    0 <= i < n ->
    0 <= j < n ->
    Znth i l 0 = Znth j l 0 ->
    i = j.

Definition fin_sequence_covers_range (n : Z) (fin_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    exists i, 0 <= i < n /\ Znth i fin_l 0 = v.

Definition base_order (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Definition order_covers_range (n : Z) (order_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    exists i, 0 <= i < n /\ Znth i order_l 0 = v.

Definition order_spec (fin_l order_l : list Z) (n : Z) : Prop :=
  fin_values_in_int_range fin_l n /\
  order_entries_in_range n order_l.

Fixpoint fin_upperbound (fin_l : list Z) (x : Z) (l : list Z) : Prop :=
  match l with
  | nil => True
  | y :: l' => Znth x fin_l 0 >= Znth y fin_l 0 /\ fin_upperbound fin_l x l'
  end.

Fixpoint fin_nonincreasing_aux (fin_l : list Z) (l : list Z) (x : Z) : Prop :=
  match l with
  | nil => True
  | y :: l' =>
      Znth x fin_l 0 >= Znth y fin_l 0 /\
      fin_nonincreasing_aux fin_l l' y
  end.

Definition fin_nonincreasing (fin_l l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: l' => fin_nonincreasing_aux fin_l l' x
  end.

Definition fin_prefix_suffix_sorted
    (fin_l l1 l2 : list Z) : Prop :=
  forall x, In x l1 -> fin_upperbound fin_l x l2.

Fixpoint last_val (default : Z) (l : list Z) : Z :=
  match l with
  | nil => default
  | x :: l' => last_val x l'
  end.

Definition phase2_order_spec (fin_l order_l : list Z) (n : Z) : Prop :=
  Zlength fin_l = n /\
  fin_values_in_int_range fin_l n /\
  list_prefix_no_dup n fin_l /\
  fin_sequence_covers_range n fin_l /\
  (forall i, 0 <= i < n -> Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) /\
  order_entries_in_range n order_l /\
  order_covers_range n order_l /\
  list_prefix_no_dup n order_l.

Definition phase2_sequence_order_spec
    (fin_l order_l : list Z) (n : Z) : Prop :=
  Zlength fin_l = n /\
  Zlength order_l = n /\
  order_l = rev fin_l.

Definition all_order_prefix_marked (n k : Z) (order_l vis_l : list Z) : Prop :=
  forall i, 0 <= i < k -> Znth (Znth i order_l 0) vis_l 0 <> 0.

Definition mutually_reachable (g : AdjGraph) (u v : Z) : Prop :=
  reachable g u v /\ reachable g v u.

Definition finish_sequence_position_before
    (fin_l : list Z) (n root c : Z) : Prop :=
  exists root_pos c_pos,
    (0 <= root_pos < n)%Z /\
    (0 <= c_pos < n)%Z /\
    Znth root_pos fin_l 0 = root /\
    Znth c_pos fin_l 0 = c /\
    root_pos < c_pos.

Definition phase1_order_graph
    (g : AdjGraph) (fin_l : list Z) (n : Z) : Prop :=
  forall root v,
    0 <= root < n ->
    0 <= v < n ->
    reachable g root v ->
    ~ reachable g v root ->
    exists c,
      0 <= c < n /\
      mutually_reachable g v c /\
      finish_sequence_position_before fin_l n root c.

Definition phase1_finished_visited (st : KSt) : Prop :=
  forall v, @Kosaraju.visited1 Z st v -> @Kosaraju.finish Z st v <> 0%nat.

Definition sid_correct_on_marked
    (g : AdjGraph) (n : Z) (vis_l sid_l : list Z) : Prop :=
  (forall u, 0 <= u < n ->
      Znth u vis_l 0 <> 0 ->
    forall v, 0 <= v < n ->
      Znth v vis_l 0 <> 0 ->
      ((Znth u sid_l 0 = Znth v sid_l 0 -> reachable g u v /\ reachable g v u) /\
       (reachable g u v /\ reachable g v u -> Znth u sid_l 0 = Znth v sid_l 0))) /\
  (forall u, 0 <= u < n ->
      Znth u vis_l 0 <> 0 ->
      0 <= Znth u sid_l 0 < n /\
      Znth (Znth u sid_l 0) vis_l 0 <> 0 /\
      Znth (Znth u sid_l 0) sid_l 0 = Znth u sid_l 0).

Definition sid_labels_in_order_prefix
    (n k : Z) (order_l vis_l sid_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    Znth v vis_l 0 <> 0 ->
    exists i, 0 <= i < k /\ Znth v sid_l 0 = Znth i order_l 0.

Definition phase2_prefix_complete
    (g : AdjGraph) (n k : Z) (order_l vis_l : list Z) : Prop :=
  forall i w,
    0 <= i < k ->
    0 <= w < n ->
    mutually_reachable g (Znth i order_l 0) w ->
    Znth w vis_l 0 <> 0.

Definition dfs2_phase2_post
    (g : AdjGraph) (n : Z)
    (vis_l sid_l vis_l_ sid_l_ : list Z) (root : Z) : Prop :=
  (forall w, 0 <= w < n ->
     Znth w vis_l 0 <> 0 ->
     Znth w vis_l_ 0 <> 0 /\ Znth w sid_l_ 0 = Znth w sid_l 0) /\
  (forall w, 0 <= w < n ->
     Znth w vis_l_ 0 <> 0 ->
     Znth w vis_l 0 = 0 ->
     Znth w sid_l_ 0 = root /\ mutually_reachable g root w) /\
  (forall w, 0 <= w < n ->
     mutually_reachable g root w ->
     Znth w vis_l_ 0 <> 0).

Definition dfs2_phase2_state
    (fin_l vis_l sid_l : list Z) (n : Z) : KSt :=
  @Kosaraju.MkSt Z 0%nat
    (fun v =>
       if Z_lt_ge_dec v 0 then 0%nat
       else if Z_lt_ge_dec v n then Z.to_nat (Znth v fin_l 0)
       else 0%nat)
    (fun _ => True)
    (fun v => 0 <= v < n /\ Znth v vis_l 0 <> 0)
    (fun v => Z.to_nat (Znth v sid_l 0))
    (Z.to_nat n).

(* The top-level phase-2 representation relation is deliberately separate
   from the cursor-local [pre_dfs2].  It records the C arrays and the fixed
   phase-1 timer/finish relation, then carries the remaining scheduled SCC
   program from C loop index [k].  This is the same residual-safeExec shape
   used by the DFS examples; prefix predicates remain available for local C
   updates, but are no longer the sole abstraction boundary. *)
Definition phase2_array_representation
    (g : AdjGraph) (fin_l order_l vis1_l vis2_l sid_l : list Z)
    (timer_v n : Z) : Prop :=
  Zlength fin_l = n /\
  Zlength order_l = n /\
  Zlength vis1_l = n /\
  Zlength vis2_l = n /\
  Zlength sid_l = n /\
  (0 <= timer_v <= n)%Z /\
  phase2_sequence_order_spec fin_l order_l n /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 <> 0%Z) /\
  pre_dfs2 g nil nil vis2_l sid_l 0
    (dfs2_phase2_state fin_l vis2_l sid_l n).

Definition phase2_residual_refinement
    (g : AdjGraph) (fin_l order_l vis1_l vis2_l sid_l : list Z)
    (timer_v n k : Z) : Prop :=
  phase2_array_representation g fin_l order_l vis1_l vis2_l sid_l timer_v n /\
  0 <= k <= n /\
  exists X : unit -> KSt -> Prop,
    safeExec (fun st => st = dfs2_phase2_state fin_l vis2_l sid_l n)
      (phase2_c_schedule g
        (fun i => Znth (Z.of_nat i) order_l 0)
        (Z.to_nat k) (Z.to_nat (n - k))) X.

Definition phase2_sequence_residual_refinement
    (g : AdjGraph) (fin_l order_l vis1_l vis2_l sid_l : list Z)
    (timer_v n k : Z) : Prop :=
  Zlength fin_l = n /\
  Zlength order_l = n /\
  Zlength vis1_l = n /\
  Zlength vis2_l = n /\
  Zlength sid_l = n /\
  (0 <= timer_v <= n)%Z /\
  (forall i, (0 <= i < n)%Z ->
     Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) /\
  (forall i, (0 <= i < n)%Z ->
     (0 <= Znth i order_l 0 < n)%Z) /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 <> 0%Z) /\
  (0 <= k <= n)%Z /\
  phase1_order_graph g fin_l n /\
  phase2_order_spec fin_l order_l n /\
  all_order_prefix_marked n k order_l vis2_l /\
  phase2_prefix_complete g n k order_l vis2_l /\
  sid_correct_on_marked g n vis2_l sid_l /\
  sid_labels_in_order_prefix n k order_l vis2_l sid_l /\
  (k = n ->
    forall u, (0 <= u < n)%Z ->
    forall v, (0 <= v < n)%Z ->
      ((Znth u sid_l 0 = Znth v sid_l 0 -> mutually_reachable g u v) /\
       (mutually_reachable g u v -> Znth u sid_l 0 = Znth v sid_l 0))).

Definition dfs2_phase2_state_post
    (g : AdjGraph) (fin_l vis_l sid_l : list Z)
    (n root : Z) (st' : KSt) : Prop :=
  let st0 := dfs2_phase2_state fin_l vis_l sid_l n in
  (forall v,
      visited2 st' v ->
      ~ visited2 st0 v ->
      mutually_reachable g root v) /\
  (forall v,
      mutually_reachable g root v ->
      ~ visited2 st0 v ->
      visited2 st' v).

Definition dfs1_timer_surplus_preserved
  (vis1_l vis1_l_ : list Z) (timer_v timer_v_ : Z) : Prop :=
  forall spare,
    0 <= spare ->
    timer_v + spare <= count_nonzero vis1_l ->
    timer_v_ + spare <= count_nonzero vis1_l_.

Definition dfs1_active_timer_surplus
  (vis1_l vis1_m : list Z) (timer_v timer_m : Z) : Prop :=
  forall spare,
    0 <= spare ->
    timer_v + spare <= count_nonzero vis1_l ->
    timer_m + spare + 1 <= count_nonzero vis1_m.

Definition dfs1_high_level_post
  (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l vis1_l_ fin_l_ : list Z)
  (u timer_v timer_v_ n : Z) : Prop :=
  adj_verts g = n /\
  csr_wf1 g radj_col_l radj_row_l vis1_l_ fin_l_ /\
  csr1_faithful g radj_col_l radj_row_l /\
  dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u /\
  dfs1_phase1_state_ready g radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ /\
  0 <= u < n /\
  0 <= timer_v <= timer_v_ /\
  timer_v <= count_nonzero vis1_l /\
  timer_v_ <= count_nonzero vis1_l_ /\
  dfs1_timer_surplus_preserved vis1_l vis1_l_ timer_v timer_v_ /\
  fin_values_in_int_range fin_l n /\
  fin_values_in_int_range fin_l_ n /\
  Znth u vis1_l_ 0 <> 0 /\
  (forall w, 0 <= w < n ->
     Znth w vis1_l 0 <> 0 -> Znth w vis1_l_ 0 <> 0) /\
  (forall w, 0 <= w < n ->
     Znth w vis1_l 0 <> 0 -> Znth w fin_l_ 0 = Znth w fin_l 0).

Definition dfs2_high_level_post
  (g : AdjGraph) (fadj_col_l fadj_row_l vis2_l sid_l vis2_l_ sid_l_ : list Z)
  (root u n : Z) : Prop :=
  adj_verts g = n /\
  csr_wf2 g fadj_col_l fadj_row_l vis2_l_ sid_l_ /\
  csr2_faithful g fadj_col_l fadj_row_l /\
  0 <= root < n /\
  0 <= u < n /\
  Znth u vis2_l_ 0 <> 0 /\
  (forall w, 0 <= w < n ->
     Znth w vis2_l 0 <> 0 -> Znth w vis2_l_ 0 <> 0).

(* The C-level dfs2 contract keeps the phase-2 continuation as [safeExec]
   and exposes these array facts separately.  This bridge is the pure
   refinement boundary used to discharge the high-level contract without
   changing that residual schedule. *)

(* Consolidated append-only helpers from group_00__dfs1-active. *)

(* Consolidated checked transpose-exit helpers. *)

