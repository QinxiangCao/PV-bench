import Algorithms.multiple_knapsack.lean.spec_lib

namespace Algorithms.multiple_knapsack.lean

open AUXLib MaxMinLib

def MKDPValueBound (dp : List Int) (capacity : Int) : Prop :=
  Zlength dp = capacity + 1 ∧
  forall cap,
    (0 ≤ cap ∧ cap ≤ capacity) →
    (0 ≤ Znth cap dp 0 ∧ Znth cap dp 0 ≤ 1000000)

def MKTransitionValue
    (old : List Int) (w v cnt capacity pos ans : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ pos ∧ pos ≤ capacity) ∧
  Zlength old = capacity + 1 ∧
  max_value_of_subset (· ≤ ·)
    (fun take =>
       (0 ≤ take ∧ take ≤ cnt) ∧
       take * w ≤ pos ∧
       (0 ≤ pos - take * w ∧ pos - take * w ≤ capacity) )
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans

def MKTransitionValueBound
    (old : List Int) (w v cnt capacity : Int) : Prop :=
  forall pos ans,
    (0 ≤ pos ∧ pos ≤ capacity) →
    MKTransitionValue old w v cnt capacity pos ans →
    (0 ≤ ans ∧ ans ≤ 1000000)

def MKQueueEntryValue
    (old q_idx q_val : List Int) (r w v pos : Int) : Prop :=
  0 ≤ Znth pos q_idx 0 ∧
  r + Znth pos q_idx 0 * w < Zlength old ∧
  Znth pos q_val 0 =
    Znth (r + Znth pos q_idx 0 * w) old 0 - Znth pos q_idx 0 * v

def MKQueueEntriesValidAfterDrop
    (old q_idx q_val : List Int) (head tail r w v k cnt : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    k - cnt ≤ Znth pos q_idx 0 ∧
    Znth pos q_idx 0 < k ∧
    MKQueueEntryValue old q_idx q_val r w v pos

def MKQueueIndexIncreasing (q_idx : List Int) (head tail : Int) : Prop :=
  forall p q,
    head ≤ p ∧ p < q ∧ q < tail →
    Znth p q_idx 0 < Znth q q_idx 0

def MKQueueValueDecreasing (q_val : List Int) (head tail : Int) : Prop :=
  forall p q,
    head ≤ p ∧ p < q ∧ q < tail →
    Znth p q_val 0 > Znth q q_val 0

def MKQueueResultValueBound
    (q_val : List Int) (head tail v k : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    (0 ≤ Znth pos q_val 0 + k * v ∧ Znth pos q_val 0 + k * v ≤ 1000000)

def MKQueueCoversWindow
    (old q_idx q_val : List Int) (head tail r w v k cnt : Int) : Prop :=
  forall cand,
    0 ≤ cand →
    cand < k →
    k - cnt ≤ cand →
    r + cand * w < Zlength old →
    exists pos,
      (head ≤ pos ∧ pos < tail) ∧
      cand ≤ Znth pos q_idx 0 ∧
      Znth pos q_idx 0 < k ∧
      Znth (r + cand * w) old 0 - cand * v ≤ Znth pos q_val 0

def MKQueueCoversWithPending
    (old q_idx q_val : List Int) (head tail r w v k cnt current : Int) : Prop :=
  forall cand,
    0 ≤ cand →
    cand < k →
    k - cnt ≤ cand →
    r + cand * w < Zlength old →
    (exists pos,
      (head ≤ pos ∧ pos < tail) ∧
      cand ≤ Znth pos q_idx 0 ∧
      Znth pos q_idx 0 < k ∧
      Znth (r + cand * w) old 0 - cand * v ≤ Znth pos q_val 0) ∨
    Znth (r + cand * w) old 0 - cand * v ≤ current

def MKQueueEntriesValidForResult
    (old q_idx q_val : List Int) (head tail r w v processed cnt : Int) : Prop :=
  forall pos,
    (head ≤ pos ∧ pos < tail) →
    processed - 1 - cnt ≤ Znth pos q_idx 0 ∧
    Znth pos q_idx 0 < processed ∧
    MKQueueEntryValue old q_idx q_val r w v pos

def MKQueueCoversResultWindow
    (old q_idx q_val : List Int) (head tail r w v processed cnt : Int) : Prop :=
  forall cand,
    0 ≤ cand →
    cand < processed →
    processed - 1 - cnt ≤ cand →
    r + cand * w < Zlength old →
    exists pos,
      (head ≤ pos ∧ pos < tail) ∧
      cand ≤ Znth pos q_idx 0 ∧
      Znth pos q_idx 0 < processed ∧
      Znth (r + cand * w) old 0 - cand * v ≤ Znth pos q_val 0

def MKZeroPrefixSafety (dp : List Int) (hi : Int) : Prop :=
  0 ≤ hi ∧ Zlength dp = hi

def MKZeroPrefixSemantics (dp : List Int) (hi : Int) : Prop :=
  forall cap, (0 ≤ cap ∧ cap < hi) → Znth cap dp 0 = 0

def MKCopyPrefixSafety
    (src dst : List Int) (j capacity : Int) : Prop :=
  (0 ≤ j ∧ j ≤ capacity + 1) ∧
  Zlength src = capacity + 1 ∧
  Zlength dst = capacity + 1

def MKCopyPrefixSemantics
    (src dst : List Int) (j : Int) : Prop :=
  forall cap, (0 ≤ cap ∧ cap < j) → Znth cap dst 0 = Znth cap src 0

def MKTransitionSafety
    (old : List Int) (w cnt capacity pos : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ pos ∧ pos ≤ capacity) ∧
  Zlength old = capacity + 1

def MKTransitionSemantics
    (old : List Int) (w v cnt capacity pos ans : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun take =>
       (0 ≤ take ∧ take ≤ cnt) ∧
       take * w ≤ pos ∧
       (0 ≤ pos - take * w ∧ pos - take * w ≤ capacity) )
    (fun take => Znth (pos - take * w) old 0 + take * v)
    ans

def MKItemResidueProgressSafety
    (old dp : List Int) (r w cnt capacity : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  0 ≤ r ∧
  r ≤ w ∧
  r ≤ capacity + 1 ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1

def MKItemResidueProgressSemantics
    (old dp : List Int) (r w v cnt capacity : Int) : Prop :=
  (forall rem k pos,
     pos = rem + k * w →
     (0 ≤ rem ∧ rem < r) →
     0 ≤ k →
     (0 ≤ pos ∧ pos ≤ capacity) →
     MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) ∧
  (forall rem k pos,
     pos = rem + k * w →
     (r ≤ rem ∧ rem < w) →
     0 ≤ k →
     (0 ≤ pos ∧ pos ≤ capacity) →
     Znth pos dp 0 = Znth pos old 0)

def MKItemResiduePrefixSafety
    (old dp : List Int) (r w cnt k capacity : Int) : Prop :=
  0 < w ∧
  0 ≤ cnt ∧
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  r ≤ capacity ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1

def MKItemResiduePrefixSemantics
    (old dp : List Int) (r w v cnt k capacity : Int) : Prop :=
  (forall t,
     (0 ≤ t ∧ t < k) →
     r + t * w ≤ capacity →
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) ∧
  forall pos,
    (0 ≤ pos ∧ pos ≤ capacity) →
    (forall rem t,
       pos = rem + t * w →
       (0 ≤ rem ∧ rem < r) →
       0 ≤ t →
       MKTransitionSemantics old w v cnt capacity pos (Znth pos dp 0)) ∧
    (forall rem t,
       pos = rem + t * w →
       (0 ≤ rem ∧ rem < w) →
       0 ≤ t →
       (r < rem ∨ (rem = r ∧ k ≤ t)) →
       Znth pos dp 0 = Znth pos old 0)

def MKQueueStorageSafety
    (old q_idx q_val : List Int) (head tail limit capacity : Int) : Prop :=
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ limit ∧
  tail ≤ Zlength q_idx ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1 ∧
  Zlength old = capacity + 1

def MKQueueDropSafety
    (old q_idx q_val : List Int)
    (head tail r w k capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  MKQueueStorageSafety old q_idx q_val head tail k capacity

def MKQueueDropSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt k : Int) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt ∧
  MKQueueResultValueBound q_val head tail v (k - 1)

def MKQueueAfterDropSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt k : Int) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWindow old q_idx q_val head tail r w v k cnt ∧
  MKQueueResultValueBound q_val head tail v k

def MKQueuePendingSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt k current : Int) : Prop :=
  MKQueueEntriesValidAfterDrop old q_idx q_val head tail r w v k cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversWithPending old q_idx q_val head tail r w v k cnt current ∧
  MKQueueResultValueBound q_val head tail v k ∧
  (0 ≤ current + k * v ∧ current + k * v ≤ 1000000)

def MKQueueResultSafety
    (old q_idx q_val : List Int)
    (head tail r w processed capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ processed ∧
  MKQueueStorageSafety old q_idx q_val head tail processed capacity

def MKQueueResultSemantics
    (old q_idx q_val : List Int)
    (head tail r w v cnt processed capacity : Int) : Prop :=
  MKQueueEntriesValidForResult old q_idx q_val head tail r w v processed cnt ∧
  MKQueueIndexIncreasing q_idx head tail ∧
  MKQueueValueDecreasing q_val head tail ∧
  MKQueueCoversResultWindow old q_idx q_val head tail r w v processed cnt ∧
  MKQueueResultValueBound q_val head tail v (processed - 1) ∧
  (head < tail →
     MKTransitionSemantics old w v cnt capacity (r + (processed - 1) * w)
       (Znth head q_val 0 + (processed - 1) * v))

def MKResidueLoopSafety
    (old dp q_idx q_val : List Int)
    (r w k head tail capacity : Int) : Prop :=
  (0 ≤ r ∧ r < w) ∧
  0 ≤ k ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  tail ≤ k ∧
  Zlength old = capacity + 1 ∧
  Zlength dp = capacity + 1 ∧
  Zlength q_idx = capacity + 1 ∧
  Zlength q_val = capacity + 1

def MKResidueLoopSemantics
    (old dp q_idx q_val : List Int)
    (r w v cnt k head tail capacity : Int) : Prop :=
  (forall t,
     (0 ≤ t ∧ t < k) →
     r + t * w ≤ capacity →
     MKTransitionSemantics old w v cnt capacity (r + t * w)
       (Znth (r + t * w) dp 0)) ∧
  MKQueueResultSemantics old q_idx q_val head tail r w v cnt k capacity

end Algorithms.multiple_knapsack.lean
