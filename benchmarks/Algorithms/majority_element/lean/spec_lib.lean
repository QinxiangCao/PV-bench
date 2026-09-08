import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.majority_element.lean

open AUXLib

def count (m : Int) : List Int → Int
  | [] => 0
  | x :: xs => (if x = m then 1 else 0) + count m xs

def IsMajorityElement (m : Int) (l : List Int) : Prop :=
  2 * count m l > (l.length : Int)

end Algorithms.majority_element.lean
