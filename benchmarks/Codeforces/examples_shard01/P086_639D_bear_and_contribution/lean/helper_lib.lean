import Codeforces.examples_shard01.P086_639D_bear_and_contribution.lean.spec_lib

namespace Codeforces.examples_shard01.P086_639D_bear_and_contribution.lean

open AUXLib

open MaxMinLib

def ZSum (l : List Int) : Int := List.foldr (· + ·) 0 l

def HeapParent (child : Int) : Int := Z.quot (child - 1) 2

def HeapOrderedFrom (l : List Int) (size lo : Int) : Prop :=
  forall child,
    0 < child →
    child < size →
    lo ≤ HeapParent child →
    Znth (HeapParent child) l 0 ≥ Znth child l 0

def HeapOrdered (l : List Int) (size : Int) : Prop :=
  HeapOrderedFrom l size 0

def ZipPerm (t0 b0 t1 b1 : List Int) : Prop :=
  Zlength b0 = Zlength t0 ∧
  Zlength t1 = Zlength t0 ∧
  Zlength b1 = Zlength t0 ∧
  List.Perm (List.zip t0 b0) (List.zip t1 b1)

def Nondecreasing (l : List Int) : Prop :=
  forall i j,
    0 ≤ i →
    i ≤ j →
    j < Zlength l →
    Znth i l 0 ≤ Znth j l 0

def HeapOrderExceptUp (l : List Int) (size child : Int) : Prop :=
  forall node,
    0 < node → node < size → node ≠ child →
    Znth (HeapParent node) l 0 ≥ Znth node l 0

def PushHoleGuard (l : List Int) (size child : Int) : Prop :=
  forall node,
    0 < node → node < size → HeapParent node = child →
    Znth (HeapParent child) l 0 ≥ Znth node l 0

def PushSiftState (l cur : List Int) (size child x : Int) : Prop :=
  Zlength cur = Zlength l ∧
  Znth child cur 0 = x ∧
  List.Perm (sublist 0 (size + 1) cur) (x :: sublist 0 size l) ∧
  HeapOrderExceptUp cur (size + 1) child ∧
  PushHoleGuard cur (size + 1) child

def HeapOrderExceptDown (l : List Int) (size index : Int) : Prop :=
  forall child,
    0 < child → child < size → HeapParent child ≠ index →
    Znth (HeapParent child) l 0 ≥ Znth child l 0

def PopHoleGuard (l : List Int) (size index : Int) : Prop :=
  index = 0 ∨
  (forall child,
     0 < child → child < size → HeapParent child = index →
     Znth (HeapParent index) l 0 ≥ Znth child l 0)

def PopSiftState (l cur : List Int) (size index : Int) : Prop :=
  Zlength cur = Zlength l ∧
  List.Perm (sublist 0 (size - 1) cur) (sublist 1 size l) ∧
  HeapOrderExceptDown cur (size - 1) index ∧
  PopHoleGuard cur (size - 1) index

def SiftState (t0 b0 t b : List Int) (size lo index : Int) : Prop :=
  ZipPerm t0 b0 t b ∧
  sublist size (Zlength t0) t = sublist size (Zlength t0) t0 ∧
  sublist size (Zlength b0) b = sublist size (Zlength b0) b0 ∧
  (forall child,
     0 < child → child < size → lo ≤ HeapParent child →
     HeapParent child ≠ index →
     Znth (HeapParent child) t 0 ≥ Znth child t 0) ∧
  (index = lo ∨
   (forall child,
      0 < child → child < size → HeapParent child = index →
      Znth (HeapParent index) t 0 ≥ Znth child t 0))

def HeapSortState (t : List Int) (n hi : Int) : Prop :=
  Nondecreasing (sublist (hi + 1) n t) ∧
  (forall p q,
     0 ≤ p → p ≤ hi → hi < q → q < n →
     Znth p t 0 ≤ Znth q t 0)

def ShiftedPrefix (values sh : List Int) (cnt : Int) : Prop :=
  forall i, (0 ≤ i ∧ i < cnt) → Znth i sh 0 = Znth i values 0 + 2000000000

def WCost (b c : Int) : Int := min b (5 * c)

def TargetPoint (s j : Int) : Int := s + Z.modulo (j - s) 5

def NormalizedBase (s j W c : Int) : Int :=
  (Z.modulo (j - s) 5) * c - (Z.div (TargetPoint s j - j) 5) * W

def CandPrefix (sh : List Int) (j W c cnt : Int) (t b : List Int) : Prop :=
  forall i, (0 ≤ i ∧ i < cnt) →
    Znth i t 0 = TargetPoint (Znth i sh 0) j ∧
    Znth i b 0 = NormalizedBase (Znth i sh 0) j W c

def SubMultiset (m l : List Int) : Prop :=
  exists rest, List.Perm l (m ++ rest)

def MinSubMultiset (l m : List Int) : Prop :=
  SubMultiset m l ∧
  (forall m',
     SubMultiset m' l → Zlength m' = Zlength m → ZSum m ≤ ZSum m')

def KSmallSum (l : List Int) (k s : Int) : Prop :=
  exists m, MinSubMultiset l m ∧ Zlength m = k ∧ s = ZSum m

def HeapContent (sb : List Int) (i : Int) (H : List Int) (hsum : Int) : Prop :=
  MinSubMultiset (sublist 0 i sb) H ∧ hsum = ZSum H

def TieCostAtResidue (values : List Int) (k b c j cost : Int) : Prop :=
  exists (chosen costs : List Int) (target : Int),
    Z.modulo target 5 = j ∧
    ChosenBloggers values k chosen ∧
    Zlength costs = k ∧
    (forall i, (0 ≤ i ∧ i < k) →
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) ∧
    cost = List.foldr (· + ·) 0 costs

def SweepValue (st sb : List Int) (k j W i v : Int) : Prop :=
  exists s,
    KSmallSum (sublist 0 (i + 1) sb) k s ∧
    v = s + k * (Z.div (Znth i st 0 - j) 5) * W

def BestState (P : Int → Prop) (best : Int) : Prop :=
  (best = -1 ∧ forall v, ¬ P v) ∨
  (0 ≤ best ∧ min_value_of_subset (· ≤ ·) P (fun x => x) best)

def ResidueBest (values : List Int) (k b c j best : Int) : Prop :=
  BestState
    (fun v => exists j', (0 ≤ j' ∧ j' < j) ∧ TieCostAtResidue values k b c j' v)
    best

def SweepSet
    (values : List Int) (k b c j : Int) (st sb : List Int) (W i : Int) (v : Int) : Prop :=
  (exists j', (0 ≤ j' ∧ j' < j) ∧ TieCostAtResidue values k b c j' v) ∨
  (exists i', k - 1 ≤ i' ∧ i' < i ∧ SweepValue st sb k j W i' v)

def SweepBest
    (values : List Int) (k b c j : Int) (st sb : List Int) (W i best : Int) : Prop :=
  BestState (SweepSet values k b c j st sb W i) best

end Codeforces.examples_shard01.P086_639D_bear_and_contribution.lean
