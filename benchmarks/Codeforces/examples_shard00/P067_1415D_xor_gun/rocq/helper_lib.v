Require Export PVbench.Codeforces.examples_shard00.P067_1415D_xor_gun.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition NoEqualBitTriplePrefix (a : list Z) (next_center : Z) : Prop :=
  forall i, 1 <= i < next_center ->
    ~ (Z.log2 (Znth (i - 1) a 0) = Z.log2 (Znth i a 0) /\
       Z.log2 (Znth i a 0) = Z.log2 (Znth (i + 1) a 0)).

Definition BitScanState (original current shifts : Z) : Prop :=
  current = Z.shiftr original shifts.

Definition PrefixXor (a : list Z) (hi : Z) : Z :=
  fold_left Z.lxor (sublist 0 hi a) 0.

Definition PrefixXorTable
    (a table : list Z) (done : Z) : Prop :=
  forall k, 0 <= k <= done -> Znth k table 0 = PrefixXor a k.

Definition DestructiveWindow
    (a : list Z) (l mid r : Z) : Prop :=
  0 <= l <= mid /\ mid < r < Zlength a /\
  Z.lxor (PrefixXor a (mid + 1)) (PrefixXor a l) >
  Z.lxor (PrefixXor a (r + 1)) (PrefixXor a (mid + 1)).

Definition WindowBefore
    (next_l next_mid next_r l mid r : Z) : Prop :=
  l < next_l \/
  (l = next_l /\
    (mid < next_mid \/ (mid = next_mid /\ r < next_r))).

Definition WindowMoveCandidate
    (a : list Z) (next_l next_mid next_r moves : Z) : Prop :=
  exists l mid r,
    DestructiveWindow a l mid r /\
    WindowBefore next_l next_mid next_r l mid r /\
    moves = r - l - 1.

Definition BruteSearchState
    (a : list Z) (next_l next_mid next_r best : Z) : Prop :=
  (best = 2147483647 /\
    forall moves, ~ WindowMoveCandidate a next_l next_mid next_r moves) \/
  min_value_of_subset Z.le
    (WindowMoveCandidate a next_l next_mid next_r)
    (fun moves => moves) best.

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.micromega.Psatz.

Require Import Coq.Arith.Wf_nat.
