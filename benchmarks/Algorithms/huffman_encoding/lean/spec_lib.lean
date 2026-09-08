import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.huffman_encoding.lean

open AUXLib MaxMinLib

inductive HuffmanTree : Type
  | HuffmanLeaf : Int → HuffmanTree
  | HuffmanNode : HuffmanTree → HuffmanTree → HuffmanTree

export HuffmanTree (HuffmanLeaf HuffmanNode)

def HuffmanLeaves : HuffmanTree → List Int
  | .HuffmanLeaf weight => [weight]
  | .HuffmanNode left_tree right_tree => HuffmanLeaves left_tree ++ HuffmanLeaves right_tree

def HuffmanTreeWeight : HuffmanTree → Int
  | .HuffmanLeaf weight => weight
  | .HuffmanNode left_tree right_tree => HuffmanTreeWeight left_tree + HuffmanTreeWeight right_tree

def HuffmanWeightedPathLength : HuffmanTree → Int
  | .HuffmanLeaf _ => 0
  | .HuffmanNode left_tree right_tree =>
      HuffmanWeightedPathLength left_tree + HuffmanWeightedPathLength right_tree +
        HuffmanTreeWeight left_tree + HuffmanTreeWeight right_tree

def HuffmanTreeFeasible (weights : List Int) (tree : HuffmanTree) : Prop :=
  List.Perm weights (HuffmanLeaves tree)

def HuffmanOptimalCost (weights : List Int) (answer : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (HuffmanTreeFeasible weights) HuffmanWeightedPathLength answer

def HuffmanInputBounded (weights : List Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength weights) → (1 ≤ Znth i weights 0 ∧ Znth i weights 0 ≤ 1000)

def HuffmanScratchFinal (weights scratch : List Int) : Prop := Znth 0 scratch 0 = sum weights

end Algorithms.huffman_encoding.lean
