import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length

namespace Data_structures.binary_indexed_tree.lean

open AUXLib

def FenwickLowbit (x : Int) : Int := Z.land x (-x)

def FenwickNodeLo (i : Int) : Int := i - FenwickLowbit i + 1

def FenwickNodeSum (a : List Int) (i : Int) : Int := sum (sublist (FenwickNodeLo i) (i+1) a)

def FenwickPrefixSum (a : List Int) (pos : Int) : Int := sum (sublist 1 (pos+1) a)

def FenwickAddArray (a : List Int) (pos delta : Int) : List Int := replace_Znth pos (Znth pos a 0+delta) a

def FenwickRep (a bit : List Int) (n : Int) : Prop :=
  Zlength a = n+1 ∧ Zlength bit = n+1 ∧ Znth 0 a 0 = 0 ∧
  ∀ i, (1 ≤ i ∧ i ≤ n) → Znth i bit 0 = FenwickNodeSum a i

def FenwickIntervalsIntSafe (a : List Int) (n : Int) : Prop :=
  ∀ lo hi, (1 ≤ lo ∧ lo ≤ hi) → hi ≤ n →
    -2147483648 ≤ sum (sublist lo (hi+1) a) ∧ sum (sublist lo (hi+1) a) ≤ 2147483647

def FenwickCovers (node target : Int) : Prop := FenwickNodeLo node ≤ target ∧ target ≤ node

def FenwickAddProgress (entry current : List Int) (n target cursor delta : Int) : Prop :=
  Zlength current = Zlength entry ∧ Znth 0 current 0 = Znth 0 entry 0 ∧
  (cursor ≤ n → FenwickCovers cursor target) ∧ ∀ node, (1 ≤ node ∧ node ≤ n) →
    ((FenwickCovers node target ∧ node < cursor) → Znth node current 0 = Znth node entry 0+delta) ∧
    ((¬ FenwickCovers node target ∨ cursor ≤ node) → Znth node current 0 = Znth node entry 0)

def FenwickQueryState (a : List Int) (target cursor accumulator : Int) : Prop :=
  accumulator + FenwickPrefixSum a cursor = FenwickPrefixSum a target

end Data_structures.binary_indexed_tree.lean
