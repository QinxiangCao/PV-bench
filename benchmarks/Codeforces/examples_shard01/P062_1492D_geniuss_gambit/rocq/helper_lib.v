Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P062_1492D_geniuss_gambit.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition GambitX (a b : Z) : list Z :=
  repeat 1 (Z.to_nat b) ++ repeat 0 (Z.to_nat a).

Definition GambitSource (a b k : Z) : Z :=
  if Z.leb k a then b - 1 else a + b - 1 - k.

Definition GambitTarget (a b k : Z) : Z :=
  if Z.leb k a then b - 1 + k else a + b - 1.

Definition GambitY (a b k : Z) : list Z :=
  if Z.eqb k 0 then GambitX a b
  else replace_Znth (GambitTarget a b k) 1
         (replace_Znth (GambitSource a b k) 0 (GambitX a b)).

Definition EncodeDigits (digits : list Z) : list Z :=
  map (fun d => d + 48) digits.

Definition CanonicalGambit (a b k : Z) : Prop :=
  GambitPair a b k (GambitX a b, GambitY a b k).

Definition GambitImpossible (a b k : Z) : Prop :=
  ~ exists q, GambitPair a b k q.
