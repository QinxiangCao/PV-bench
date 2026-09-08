import Algorithms.sliding_window_maximum.lean.spec_lib

namespace Algorithms.sliding_window_maximum.lean

open AUXLib

def SWMOutputPrefixShape (l : List Int) (k out_idx : Int) (out : List Int) : Prop :=
  1 ≤ k ∧ k ≤ Zlength l ∧ (0 ≤ out_idx ∧ out_idx ≤ Zlength l-k+1) ∧ Zlength out = out_idx

def SWMQueueStorageSafe (l q_l : List Int) (head tail processed : Int) : Prop :=
  Zlength q_l = Zlength l ∧ (0 ≤ processed ∧ processed ≤ Zlength l) ∧
  (0 ≤ head ∧ head ≤ tail) ∧ tail ≤ processed ∧
  ∀ pos, (head ≤ pos ∧ pos < tail) → 0 ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < Zlength l

def SWMOutputPrefix (l : List Int) (k out_idx : Int) (out : List Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < out_idx) → WindowMaxValue l idx (idx+k) (Znth idx out 0)

def SWMQueueEntriesInWindow (q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ pos, (head ≤ pos ∧ pos < tail) → lo ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < hi

def SWMQueueEntriesInOpenWindow (q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ pos, (head ≤ pos ∧ pos < tail) → lo < Znth pos q_l 0 ∧ Znth pos q_l 0 < hi

def SWMQueueIndexIncreasing (q_l : List Int) (head tail : Int) : Prop :=
  ∀ p q, (head ≤ p ∧ p < q ∧ q < tail) → Znth p q_l 0 < Znth q q_l 0

def SWMQueueValueDecreasing (l q_l : List Int) (head tail : Int) : Prop :=
  ∀ p q, (head ≤ p ∧ p < q ∧ q < tail) → Znth (Znth p q_l 0) l 0 > Znth (Znth q q_l 0) l 0

def SWMQueueCoversWindow (l q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < Zlength l) → (lo ≤ idx ∧ idx < hi) →
    ∃ pos, (head ≤ pos ∧ pos < tail) ∧ (idx ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < hi) ∧
      Znth idx l 0 ≤ Znth (Znth pos q_l 0) l 0

def SWMQueueCoversOpenWindow (l q_l : List Int) (head tail lo hi : Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < Zlength l) → (lo < idx ∧ idx < hi) →
    ∃ pos, (head ≤ pos ∧ pos < tail) ∧ (idx ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < hi) ∧
      Znth idx l 0 ≤ Znth (Znth pos q_l 0) l 0

def SWMQueueCoversWithPending (l q_l : List Int) (head tail lo i : Int) : Prop :=
  ∀ idx, (0 ≤ idx ∧ idx < Zlength l) → (lo < idx ∧ idx < i) →
    (∃ pos, (head ≤ pos ∧ pos < tail) ∧ (idx ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < i) ∧
      Znth idx l 0 ≤ Znth (Znth pos q_l 0) l 0) ∨ Znth idx l 0 ≤ Znth i l 0

def SWMQueueDropLoopState (l q_l : List Int) (head tail i k : Int) : Prop :=
  SWMQueueEntriesInWindow q_l head tail (i-k) i ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversOpenWindow l q_l head tail (i-k) i

def SWMQueueAfterDrop (l q_l : List Int) (head tail i k : Int) : Prop :=
  SWMQueueEntriesInOpenWindow q_l head tail (i-k) i ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversOpenWindow l q_l head tail (i-k) i

def SWMQueuePendingState (l q_l : List Int) (head tail i k : Int) : Prop :=
  SWMQueueEntriesInOpenWindow q_l head tail (i-k) i ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversWithPending l q_l head tail (i-k) i

def SWMQueueState (l q_l : List Int) (head tail processed k : Int) : Prop :=
  SWMQueueEntriesInWindow q_l head tail (processed-k) processed ∧ SWMQueueIndexIncreasing q_l head tail ∧
  SWMQueueValueDecreasing l q_l head tail ∧ SWMQueueCoversWindow l q_l head tail (processed-k) processed ∧
  ((head < tail ∧ k ≤ processed) → WindowMaxValue l (processed-k) processed (Znth (Znth head q_l 0) l 0))

end Algorithms.sliding_window_maximum.lean
