Require Export PVbench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* The processed region is a subset of the original mathematical solution set,
   ordered by the primitive ratio of each pair. *)
Definition RCgcd : Z -> Z -> Z := Z.gcd.

Definition RCBefore (p q : Z) (ab : Z * Z) : Prop :=
  let g := Z.gcd (fst ab) (snd ab) in
  fst ab / g < p \/ (fst ab / g = p /\ snd ab / g < q).

Definition RCProgress (n m p q ans : Z) : Prop :=
  ans = #(fun ab : Z * Z =>
    ((1 <= fst ab < n + 1 /\ 1 <= snd ab < m + 1) /\
     (fst ab + snd ab | snd ab * Z.gcd (fst ab) (snd ab))) /\
    RCBefore p q ab).

Require Import Coq.micromega.Lia.

Require Import Coq.Sorting.Permutation.
