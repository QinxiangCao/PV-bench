Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.
Require Import PVbench.Codeforces.examples_shard01.P039_435B_pasha_maximizes.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

(* Lexicographic comparison, stated independently of any implementation. *)
Definition LexLe (a b : list Z) : Prop :=
  a = b \/
  (exists i,
      0 <= i < Z.min (Zlength a) (Zlength b) /\
      (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
      Znth i a 0 < Znth i b 0) \/
  (Zlength a < Zlength b /\ is_prefix a b).

Definition PrefixEq (a b : list Z) (i : Z) : Prop :=
  Zlength a = Zlength b /\
  0 <= i <= Zlength a /\
  forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0.

(* The first [pos] digits are already globally optimal.  Every competitor is
   either lexicographically no larger, or agrees on that prefix and remains
   attainable from the current suffix using the unspent budget. *)
Definition GreedyProgress
    (input : list Z) (budget : Z) (current : list Z)
    (pos remaining : Z) : Prop :=
  Zlength current = Zlength input /\
  0 <= pos <= Zlength input /\
  0 <= remaining <= budget /\
  SwapReach input current (budget - remaining) /\
  forall q, SwapReach input q budget ->
    LexLe q current \/
    (PrefixEq q current pos /\ SwapReach current q remaining).

(* [best] is the leftmost maximum of the inspected interval [lo, hi). *)
Definition FirstMaximumPrefix
    (l : list Z) (lo hi best : Z) : Prop :=
  0 <= lo < hi /\ hi <= Zlength l /\ lo <= best < hi /\
  (forall p, lo <= p < hi -> Znth p l 0 <= Znth best l 0) /\
  (forall p, lo <= p < best -> Znth p l 0 < Znth best l 0).

(* The final scan interval consists precisely of positions reachable with the
   remaining adjacent-swap budget. *)
Definition ReachableFirstMaximum
    (l : list Z) (pos remaining best : Z) : Prop :=
  FirstMaximumPrefix l pos (Z.min (Zlength l) (pos + remaining + 1)) best.

(* Move one list element left while preserving the relative order of all
   other elements.  This is the mathematical effect of any implementation of
   that rearrangement, not an encoding of the C loop. *)
Definition move_left (l : list Z) (from to : Z) : list Z :=
  sublist 0 to l ++
  [Znth from l 0] ++
  sublist to from l ++
  sublist (from + 1) (Zlength l) l.

(* A selected leftmost maximum is an exchange point when moving it to [pos]
   cannot make an already smaller competitor larger, and every competitor
   still tied on the processed prefix has a residual path after the movement
   cost is subtracted.  This is the semantic fact needed between selection
   and the concrete bubbling implementation. *)
Definition GreedyExchangeClosure
    (current : list Z) (pos remaining best : Z) : Prop :=
  let moved := move_left current best pos in
  let residual := remaining - (best - pos) in
  (forall q, LexLe q current -> LexLe q moved) /\
  (forall q,
      PrefixEq q current pos ->
      SwapReach current q remaining ->
      LexLe q moved \/
      (PrefixEq q moved (pos + 1) /\ SwapReach moved q residual)).

(* Exchange readiness belongs to the state at the start of a greedy phase,
   rather than being manufactured by either scan-exit branch.  It quantifies
   over the mathematical result of the bounded maximum selection, so the
   concrete scan may refine [best] without changing this fact. *)
Definition GreedySelectionReady
    (current : list Z) (pos remaining : Z) : Prop :=
  forall best,
    ReachableFirstMaximum current pos remaining best ->
    GreedyExchangeClosure current pos remaining best.
