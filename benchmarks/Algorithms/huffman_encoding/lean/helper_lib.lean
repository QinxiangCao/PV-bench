import Algorithms.huffman_encoding.lean.spec_lib

namespace Algorithms.huffman_encoding.lean

open AUXLib MaxMinLib

def HuffmanResidualOptimum (input live : List Int) (accumulated : Int) : Prop :=
  sum live = sum input ∧ ∃ remaining, HuffmanOptimalCost live remaining ∧ HuffmanOptimalCost input (accumulated + remaining)

def HuffmanProgress (input scratch : List Int) (active accumulated : Int) : Prop :=
  HuffmanResidualOptimum input (sublist 0 active scratch) accumulated

def HuffmanMinScan (scratch : List Int) (scanned best : Int) : Prop :=
  ∀ k, (0 ≤ k ∧ k < scanned) → Znth best scratch 0 ≤ Znth k scratch 0

def HuffmanFirstHeld (input scratch : List Int) (active held accumulated : Int) : Prop :=
  ∃ prior_live, List.Perm prior_live (held :: sublist 0 active scratch) ∧
    (∀ weight, weight ∈ prior_live → held ≤ weight) ∧ HuffmanResidualOptimum input prior_live accumulated

def HuffmanPairReady (input scratch : List Int) (active first second accumulated : Int) : Prop :=
  ∃ prior_live, List.Perm prior_live (first :: second :: sublist 0 active scratch) ∧
    (∀ weight, weight ∈ prior_live → first ≤ weight) ∧
    (∀ weight, weight ∈ (second :: sublist 0 active scratch) → second ≤ weight) ∧
    HuffmanResidualOptimum input prior_live accumulated

end Algorithms.huffman_encoding.lean
