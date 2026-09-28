Require Export PVbench.Codeforces.examples_shard00.P063_1977C_nikita_and_lcm.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition GcdValue (a b : Z) : Z :=
  Z.gcd a b.

Definition LcmCapValue (a b cap out : Z) : Prop :=
  let exact := Z.lcm a b in
  out = if exact <=? cap then exact else cap + 1.

Definition CompareResult (a b out : Z) : Prop :=
  (a > b /\ out = 1) \/
  (a < b /\ out = -1) \/
  (a = b /\ out = 0).

Require Import Coq.Sorting.Permutation.

Definition CopyMaxState
    (input copied : list Z) (processed mx : Z) : Prop :=
  copied = sublist 0 processed input /\
  ((processed = 0 /\ mx = 0) \/
   (0 < processed /\
    max_value_of_subset Z.le
      (fun i : Z => 0 <= i < processed)
      (fun i => Znth i input 0) mx)).

Definition LcmPrefixState
    (values : list Z) (processed cap acc : Z) : Prop :=
  exists exact,
    LeastCommonOfChosen values (fun i : Z => 0 <= i < processed) exact /\
    acc = if exact <=? cap then exact else cap + 1.

Definition PrefixContains
    (values : list Z) (processed d : Z) : Prop :=
  exists i, 0 <= i < processed /\ Znth i values 0 = d.

Definition PrefixDividingIndex
    (values : list Z) (d processed i : Z) : Prop :=
  0 <= i < processed /\ (Znth i values 0 | d).

Definition DivisorScanState
    (values : list Z) (d processed present count acc : Z) : Prop :=
  (present = 0 \/ present = 1) /\
  (present = 1 <-> PrefixContains values processed d) /\
  count = #(PrefixDividingIndex values d processed) /\
  exists exact,
    LeastCommonOfChosen values
      (PrefixDividingIndex values d processed) exact /\
    acc = if exact <=? d then exact else d + 1.

Definition FullDividingIndex
    (values : list Z) (d i : Z) : Prop :=
  0 <= i < Zlength values /\ (Znth i values 0 | d).

Definition DivisorCandidateCount
    (values : list Z) (d count : Z) : Prop :=
  ~ In d values /\
  count = #(FullDividingIndex values d) /\
  LeastCommonOfChosen values (FullDividingIndex values d) d.

Definition EnumeratedDivisor
    (mx q z d : Z) : Prop :=
  (exists r,
      1 <= r < q /\
      r * r <= mx /\
      mx mod r = 0 /\
      (d = r \/ d = mx / r)) \/
  (mx mod q = 0 /\ q * q <= mx /\
   ((1 <= z /\ d = q) \/ (2 <= z /\ d = mx / q))).

Definition EnumeratedScore
    (values : list Z) (mx q z score : Z) : Prop :=
  score = 0 \/
  exists d,
    EnumeratedDivisor mx q z d /\
    DivisorCandidateCount values d score.

Definition DivisorBestState
    (values : list Z) (mx q z ans : Z) : Prop :=
  max_value_of_subset Z.le
    (EnumeratedScore values mx q z)
    (fun score => score) ans.

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.ZArith.Zquot.
