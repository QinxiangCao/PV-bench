import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ListLib.Interval

namespace Codeforces.examples_shard01.P017_753A_santa_claus_and_candies.lean

open AUXLib

open MaxMinLib

def CandyAllocation (n : Int) (xs : List Int) : Prop :=
  Forall (fun x => x > 0) xs ∧ xs.Nodup ∧ xs.foldr (· + ·) 0 = n

def Pre (n : Int) : Prop := True

def Spec (n : Int) (out : List Int) : Prop :=
  max_object_of_subset (· ≤ ·) (CandyAllocation n) (fun ys => Zlength ys) out

end Codeforces.examples_shard01.P017_753A_santa_claus_and_candies.lean
