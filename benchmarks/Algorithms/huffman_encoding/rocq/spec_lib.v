Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive HuffmanTree : Type :=
  | HuffmanLeaf : Z -> HuffmanTree
  | HuffmanNode : HuffmanTree -> HuffmanTree -> HuffmanTree.
Fixpoint HuffmanLeaves (tree : HuffmanTree) : list Z :=
  match tree with
  | HuffmanLeaf weight => [weight]
  | HuffmanNode left_tree right_tree =>
      HuffmanLeaves left_tree ++ HuffmanLeaves right_tree
  end.
Fixpoint HuffmanTreeWeight (tree : HuffmanTree) : Z :=
  match tree with
  | HuffmanLeaf weight => weight
  | HuffmanNode left_tree right_tree =>
      HuffmanTreeWeight left_tree + HuffmanTreeWeight right_tree
  end.

(** Weighted external path length.  Joining two subtrees increases every leaf
    depth below the new root by one, hence adds both subtree weights. *)
Fixpoint HuffmanWeightedPathLength (tree : HuffmanTree) : Z :=
  match tree with
  | HuffmanLeaf _ => 0
  | HuffmanNode left_tree right_tree =>
      HuffmanWeightedPathLength left_tree +
      HuffmanWeightedPathLength right_tree +
      HuffmanTreeWeight left_tree + HuffmanTreeWeight right_tree
  end.
Definition HuffmanTreeFeasible
    (weights : list Z) (tree : HuffmanTree) : Prop :=
  Permutation weights (HuffmanLeaves tree).

(** Public mathematical result: [answer] is the minimum weighted external
    path length over all full binary trees with exactly the input leaf-weight
    multiset.  The minimization is deliberately the repository MaxMinLib
    interface, not a custom minimum relation or an algorithm-generated set. *)
Definition HuffmanOptimalCost
    (weights : list Z) (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (HuffmanTreeFeasible weights)
    HuffmanWeightedPathLength
    answer.
Definition HuffmanInputBounded (weights : list Z) : Prop :=
  forall i,
    0 <= i < Zlength weights ->
    1 <= Znth i weights 0 <= 1000.

(** The scratch array's only public value-level commitment: its surviving
    live root has the sum of all input frequencies.  Remaining cells are
    intentionally unconstrained. *)
Definition HuffmanScratchFinal
    (weights scratch : list Z) : Prop :=
  Znth 0 scratch 0 = sum weights.

(** Internal mathematical interface shared by the merge-loop phases.  It says
    that solving the current residual instance and adding the already charged
    merge cost gives a genuine optimum for the original input. *)
