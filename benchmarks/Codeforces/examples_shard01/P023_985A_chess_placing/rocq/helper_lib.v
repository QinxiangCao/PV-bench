Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition OddTarget (i : Z) : Z := 2 * i + 1.

Definition EvenTarget (i : Z) : Z := 2 * i + 2.

Definition ChessCostPrefix
    (sorted : list Z) (done odd even : Z) : Prop :=
  odd = sum (fun i : Z => 0 <= i < done)
            (fun i => Z.abs (Znth i sorted 0 - OddTarget i)) /\
  even = sum (fun i : Z => 0 <= i < done)
             (fun i => Z.abs (Znth i sorted 0 - EvenTarget i)).
