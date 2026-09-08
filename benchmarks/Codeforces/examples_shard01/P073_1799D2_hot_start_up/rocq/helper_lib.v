Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P073_1799D2_hot_start_up.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition DP_INF : Z := 4557430888798830399.

(* After a nonempty prefix, the cpu that ran the final position is the active
   cpu.  [other] is zero when the other cpu has never run; otherwise it is the
   program at the last position assigned to that other cpu. *)

Definition OtherCpuLastProgram (prog cpu : list Z) (other : Z) : Prop :=
  0 < Zlength prog /\
  Zlength cpu = Zlength prog /\
  let active := Znth (Zlength prog - 1) cpu 0 in
  (other = 0 /\
     forall q, 0 <= q < Zlength prog -> Znth q cpu 0 = active) \/
  (exists q,
     0 <= q < Zlength prog /\
     Znth q cpu 0 <> active /\
     other = Znth q prog 0 /\
     forall r, q < r < Zlength prog -> Znth r cpu 0 = active).

(* A schedule cost belonging to the state indexed by [other] after exactly
   [prefix_len] jobs have been processed. *)

Definition PrefixStateCost
    (prog cold hot : list Z) (prefix_len other total : Z) : Prop :=
  exists cpu,
    RunCost (sublist 0 prefix_len prog) cold hot cpu total /\
    OtherCpuLastProgram (sublist 0 prefix_len prog) cpu other.

Definition PrefixStateMinimum
    (prog cold hot : list Z) (prefix_len other total : Z) : Prop :=
  min_value_of_subset Z.le
    (PrefixStateCost prog cold hot prefix_len other)
    (fun x => x) total.

(* A finite cell stores its state minimum relative to the common offset;
   DP_INF is used exactly when the corresponding schedule class is empty. *)

Definition NormalizedScheduleCell
    (prog cold hot : list Z) (prefix_len other off value : Z) : Prop :=
  (value < DP_INF /\
   PrefixStateMinimum prog cold hot prefix_len other (off + value)) \/
  (value = DP_INF /\
   ~ exists total, PrefixStateCost prog cold hot prefix_len other total).

(* Mathematical meaning of the normalized DP vector at a main-loop head.
   Machine ranges, list lengths, and all spatial ownership remain explicit in
   the C invariant; this predicate owns only schedule-cost semantics. *)

Definition NormalizedScheduleState
    (prog cold hot : list Z) (prefix_len : Z)
    (dp : list Z) (off mind : Z) : Prop :=
  (forall other,
     0 <= other <= Zlength cold ->
     NormalizedScheduleCell prog cold hot prefix_len other off
       (Znth other dp DP_INF)) /\
  min_value_of_subset Z.le
    (fun value =>
       exists other,
         0 <= other <= Zlength cold /\
         value = Znth other dp DP_INF /\
         value < DP_INF)
    (fun x => x) mind /\
  Spec (sublist 0 prefix_len prog) cold hot (off + mind).
