Require Export PVbench.Algorithms.huffman_encoding.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** Internal mathematical interface shared by the merge-loop phases.  It says
    that solving the current residual instance and adding the already charged
    merge cost gives a genuine optimum for the original input. *)
Definition HuffmanResidualOptimum
    (input live : list Z) (accumulated : Z) : Prop :=
  sum live = sum input /\
  exists remaining,
    HuffmanOptimalCost live remaining /\
    HuffmanOptimalCost input (accumulated + remaining).

Definition HuffmanProgress
    (input scratch : list Z) (active accumulated : Z) : Prop :=
  HuffmanResidualOptimum input (sublist 0 active scratch) accumulated.

(** Public selection facts use the same library minimum as the final optimum.
    The prefix is the mathematical candidate domain; all storage and machine
    constraints remain explicit in the C annotations. *)
Definition HuffmanMinScan (scratch : list Z) (scanned best : Z) : Prop :=
  min_value_of_subset Z.le
    (fun k : Z => 0 <= k < scanned)
    (fun k => Znth k scratch 0) (Znth best scratch 0).

Definition HuffmanFirstHeld (input scratch : list Z)
    (active held accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live (held :: sublist 0 active scratch) /\
    min_value_of_subset Z.le (fun weight => In weight prior_live)
      (fun weight : Z => weight) held /\
    HuffmanResidualOptimum input prior_live accumulated.
