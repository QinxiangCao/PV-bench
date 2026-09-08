(* Codeforces 1027/G - X-mouse in the Campus: the mouse moves from room i to
   i * x mod m each second from an unknown start; fewest traps that catch it. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* traps is a set of distinct rooms in [0, m) that catches the mouse wherever it
   starts: for every start there is a time t >= 0 with start * x^t mod m trapped. *)
Definition CatchesAll (m x : Z) (traps : list Z) : Prop :=
  NoDup traps /\ Forall (fun r => 0 <= r < m) traps /\
  forall start, 0 <= start < m -> exists t room, t >= 0 /\ room = start * Z.pow x t mod m /\ In room traps.

(* gcd(x, m) = 1; the bounds 2 <= m <= 10^14 and 1 <= x < m are stated in the
   solver Require instead, so they are commented out here. *)
Definition Pre (m x : Z) : Prop :=
  (* Stated explicitly in the P090 solver Require, so dropped here:
       2<=m<=Z.pow 10 14 /\ 1<=x<m /\ *)
  Z.gcd x m = 1.

(* out = min { |traps| : CatchesAll m x traps }. *)
Definition Spec (m x out : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists traps, CatchesAll m x traps /\ v = Zlength traps) (fun x => x) out.
