Require Import PVbench.Algorithms.huffman_encoding.rocq.spec_lib.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition HuffmanResidualOptimum
    (input live : list Z) (accumulated : Z) : Prop :=
  sum live = sum input /\
  exists remaining,
    HuffmanOptimalCost live remaining /\
    HuffmanOptimalCost input (accumulated + remaining).
Definition HuffmanProgress
    (input scratch : list Z) (active accumulated : Z) : Prop :=
  HuffmanResidualOptimum input (sublist 0 active scratch) accumulated.

(** [best] denotes a minimum of the already scanned prefix.  Bounds for
    [best], [scanned], and concrete array access deliberately remain in C. *)
Definition HuffmanMinScan
    (scratch : list Z) (scanned best : Z) : Prop :=
  forall k,
    0 <= k < scanned ->
    Znth best scratch 0 <= Znth k scratch 0.

(** One globally minimum residual weight has been removed from scratch and is
    held in the local [held].  The remaining live prefix plus that value is
    the prior residual multiset. *)
Definition HuffmanFirstHeld
    (input scratch : list Z)
    (active held accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live (held :: sublist 0 active scratch) /\
    (forall weight, In weight prior_live -> held <= weight) /\
    HuffmanResidualOptimum input prior_live accumulated.

(** Both greedy-smallest values are held and [scratch[0..active)] is the rest
    of the prior residual multiset.  This is the implementation-independent
    premise of the Huffman greedy-choice theorem. *)
Definition HuffmanPairReady
    (input scratch : list Z)
    (active first second accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live
      (first :: second :: sublist 0 active scratch) /\
    (forall weight, In weight prior_live -> first <= weight) /\
    (forall weight,
      In weight (second :: sublist 0 active scratch) -> second <= weight) /\
    HuffmanResidualOptimum input prior_live accumulated.

(** Proof-support infrastructure for the structural Huffman greedy-choice
    argument.  These declarations are intentionally independent of the C
    implementation and of the public [HuffmanOptimalCost] candidate space. *)
