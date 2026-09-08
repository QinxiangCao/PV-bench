
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Occurrences (v : Z) (l : list Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l v).

(** Mathematical meaning of the counters after scanning the prefix [0, i).
    The sentinel [-1] is outside the input range, so [y = -1] precisely
    denotes that no second value has been observed. *)
Definition PaintScanState
    (a : list Z) (i x y cx cy : Z) : Prop :=
  0 <= i <= Zlength a /\
  x = Znth 0 a 0 /\
  0 <= cx <= i /\
  0 <= cy <= i /\
  cx + cy = i /\
  (y = -1 <-> cy = 0) /\
  (y <> -1 -> y <> x) /\
  cx = Occurrences x (sublist 0 i a) /\
  (y <> -1 -> cy = Occurrences y (sublist 0 i a)) /\
  (forall j, 0 <= j < i ->
    Znth j a 0 = x \/ (y <> -1 /\ Znth j a 0 = y)).
