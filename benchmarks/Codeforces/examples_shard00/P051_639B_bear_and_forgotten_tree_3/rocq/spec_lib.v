Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import GraphLib.graph_basic.

Require Import GraphLib.reachable.vpath.

Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.

Local Open Scope Z_scope.

Definition TreeVertex (n v : Z) : Prop :=
  1 <= v <= n.

Definition RememberedGraph (n : Z) (e : list (Z * Z)) : ZGraph :=
  {| zv := TreeVertex n;
     ze := fun x y => In (x,y) e \/ In (y,x) e |}.

Definition PathInEdges (n : Z) (e : list (Z * Z)) (p : list Z) : Prop :=
  0 < Zlength p /\ NoDup p /\
  valid_vpath (RememberedGraph n e) (Znth 0 p 0) p
    (Znth (Zlength p - 1) p 0).

Definition RootPathInEdges (n : Z) (e : list (Z * Z))
    (p : list Z) : Prop :=
  PathInEdges n e p /\ Znth 0 p 0 = 1.

(** The edge at index [k] gives the sole parent of vertex [k+2].
    Parents have smaller positive numbers, so repeatedly following parents
    is well-founded and reaches the root; all edge endpoints lie in [1,n]. *)
Definition IncreasingParentTree (n : Z) (e : list (Z * Z)) : Prop :=
  Zlength e = n - 1 /\
  forall k, 0 <= k < n - 1 ->
    exists parent,
      Znth k e (0, 0) = (parent, k + 2) /\
      1 <= parent < k + 2.

(** This is the reusable metric consequence of the rooted-tree certificate:
    every simple endpoint path is controlled by the two root arms, each of
    which has length at most [h].  Keeping it explicit in the certificate
    exposes exactly the tree theorem needed by infeasibility proofs. *)
Definition PathsControlledByRootHeight
    (n : Z) (e : list (Z * Z)) (h : Z) : Prop :=
  forall p, PathInEdges n e p -> Zlength p - 1 <= 2 * h.

Definition ValidRememberedTree (n d h : Z) (e : list (Z * Z)) : Prop :=
  IncreasingParentTree n e /\
  (forall v, 1 <= v <= n ->
    exists p, PathInEdges n e p /\
      Znth 0 p 0 = 1 /\ Znth (Zlength p - 1) p 0 = v) /\
  max_value_of_subset Z.le (RootPathInEdges n e)
    (fun p => Zlength p - 1) h /\
  max_value_of_subset Z.le (PathInEdges n e)
    (fun p => Zlength p - 1) d /\
  PathsControlledByRootHeight n e h.

Definition Pre (n d h : Z) : Prop :=
  2 <= n <= 100000 /\ 1 <= h <= d /\ d <= n - 1.

Definition Spec (n d h : Z) (out : option (list (Z * Z))) : Prop :=
  (exists e, out = Some e /\ ValidRememberedTree n d h e) \/
  (out = None /\ forall e, ~ ValidRememberedTree n d h e).
