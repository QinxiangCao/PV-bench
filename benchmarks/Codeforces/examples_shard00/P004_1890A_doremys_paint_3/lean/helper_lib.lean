import Codeforces.examples_shard00.P004_1890A_doremys_paint_3.lean.spec_lib

namespace Codeforces.examples_shard00.P004_1890A_doremys_paint_3.lean

open AUXLib

def Occurrences (v : Int) (l : List Int) : Int := (l.count v : Int)

def PaintScanState (a : List Int) (i x y cx cy : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength a) ∧ x = Znth 0 a 0 ∧
  (0 ≤ cx ∧ cx ≤ i) ∧ (0 ≤ cy ∧ cy ≤ i) ∧ cx + cy = i ∧
  (y = -1 ↔ cy = 0) ∧ (y ≠ -1 → y ≠ x) ∧ cx = Occurrences x (sublist 0 i a) ∧
  (y ≠ -1 → cy = Occurrences y (sublist 0 i a)) ∧
  (∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = x ∨ (y ≠ -1 ∧ Znth j a 0 = y))

end Codeforces.examples_shard00.P004_1890A_doremys_paint_3.lean
