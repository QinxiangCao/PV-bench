Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P058_1721D_maximum_and.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition MaskedLeft (a : list Z) (mask : Z) : list Z :=
  map (fun x => Z.land x mask) a.

Definition MaskedComplementRight (b : list Z) (mask : Z) : list Z :=
  map (fun x => Z.land (Z.lnot x) mask) b.

Definition MaskFeasible (a b : list Z) (mask : Z) : Prop :=
  Permutation (MaskedLeft a mask) (MaskedComplementRight b mask).

Definition MaskedBuffersPrefix
    (a b : list Z) (mask : Z)
    (ka kb : list Z) (upto : Z) : Prop :=
  ka = MaskedLeft (sublist 0 upto a) mask /\
  kb = MaskedComplementRight (sublist 0 upto b) mask.

Definition GreedyMaskPrefixOptimal
    (a b : list Z) (bit ans : Z) : Prop :=
  MaskFeasible a b ans /\
  ans = Z.shiftl (Z.shiftr ans (bit + 1)) (bit + 1) /\
  forall v,
    AndCandidate a b v ->
    Z.shiftr v (bit + 1) <= Z.shiftr ans (bit + 1).
