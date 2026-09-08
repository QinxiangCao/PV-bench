From Coq Require Import ZArith List Lia.
Require Import Coq.ZArith.Zbitwise.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

(** The C expression [x & (-x)] is interpreted as [Z.land x (-x)]. *)
Definition FenwickLowbit (x : Z) : Z :=
  Z.land x (-x).

(** A Fenwick node [i] covers the closed 1-based interval
    [[i - lowbit(i) + 1, i]]. *)
Definition FenwickNodeLo (i : Z) : Z :=
  i - FenwickLowbit i + 1.

Definition FenwickNodeSum (a : list Z) (i : Z) : Z :=
  sum (sublist (FenwickNodeLo i) (i + 1) a).

(** [FenwickPrefixSum a pos] is exactly the sum of the closed interval
    [[1,pos]].  In particular, [pos = 0] denotes the empty interval. *)
Definition FenwickPrefixSum (a : list Z) (pos : Z) : Z :=
  sum (sublist 1 (pos + 1) a).

Definition FenwickAddArray
    (a : list Z) (pos delta : Z) : list Z :=
  replace_Znth pos (Znth pos a 0 + delta) a.

(** A length-[n+1] concrete tree represents the 1-based logical array
    [a[1..n]].  Slot zero is reserved and is not part of any represented
    sum.  Every node equation below names its exact closed interval. *)
Definition FenwickRep
    (a bit : list Z) (n : Z) : Prop :=
  Zlength a = n + 1 /\
  Zlength bit = n + 1 /\
  Znth 0 a 0 = 0 /\
  forall i,
    1 <= i <= n ->
    Znth i bit 0 = FenwickNodeSum a i.

(** This implementation uses signed [int].  Requiring every closed
    subinterval of [a[1..n]] to fit makes every Fenwick node and every
    partial accumulator used by [query] representable. *)
Definition FenwickIntervalsIntSafe (a : list Z) (n : Z) : Prop :=
  forall lo hi,
    1 <= lo <= hi ->
    hi <= n ->
    -2147483648 <= sum (sublist lo (hi + 1) a) <= 2147483647.

Definition FenwickCovers (node target : Z) : Prop :=
  FenwickNodeLo node <= target <= node.

(** Internal state of [add].  Nodes are ordered by their 1-based node
    index: covering nodes already below [cursor] have received [delta], and
    every other node is still equal to the entry tree.  If [cursor] is live,
    it is itself the next covering node. *)
Definition FenwickAddProgress
    (entry current : list Z) (n target cursor delta : Z) : Prop :=
  Zlength current = Zlength entry /\
  Znth 0 current 0 = Znth 0 entry 0 /\
  (cursor <= n -> FenwickCovers cursor target) /\
  forall node,
    1 <= node <= n ->
    ((FenwickCovers node target /\ node < cursor) ->
       Znth node current 0 = Znth node entry 0 + delta) /\
    ((~ FenwickCovers node target \/ cursor <= node) ->
       Znth node current 0 = Znth node entry 0).

(** Internal state of [query].  The accumulator contains the disjoint
    closed node intervals already removed from the original closed prefix;
    [[1,cursor]] is exactly the unconsumed prefix. *)
Definition FenwickQueryState
    (a : list Z) (target cursor accumulator : Z) : Prop :=
  accumulator + FenwickPrefixSum a cursor = FenwickPrefixSum a target.

(** The following lemmas are integer-level bridges for symbolic execution;
    they do not assume a machine-specific bit-vector axiom. *)

