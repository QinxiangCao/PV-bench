import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.split_array_largest_sum.lean

open AUXLib MaxMinLib

def SegmentPartition (l : List Int) (parts : List (List Int)) : Prop :=
  parts ≠ [] ∧ parts.flatten = l ∧ Forall (fun seg => seg ≠ []) parts

def MaxSegmentSum (parts : List (List Int)) (max_sum : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun seg => seg ∈ parts) (fun seg => sum seg) max_sum

def PartitionMaxSegmentSum (l : List Int) (m max_sum : Int) : Prop :=
  ∃ parts, SegmentPartition l parts ∧ Zlength parts = m ∧ MaxSegmentSum parts max_sum

def MinimizedMaxSegmentSum (l : List Int) (m answer : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun max_sum => PartitionMaxSegmentSum l m max_sum) (fun max_sum => max_sum) answer

end Algorithms.split_array_largest_sum.lean
