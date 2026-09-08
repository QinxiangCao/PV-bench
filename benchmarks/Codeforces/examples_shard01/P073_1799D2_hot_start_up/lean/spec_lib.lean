import ListLib.General.Length
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P073_1799D2_hot_start_up.lean

open AUXLib

open MaxMinLib

def HotStart (prog cpu : List Int) (i j : Int) : Prop :=
  (0 ≤ j ∧ j < i) ∧ Znth j cpu 0 = Znth i cpu 0 ∧
    (∀ q, (j < q ∧ q < i) → Znth q cpu 0 ≠ Znth i cpu 0) ∧ Znth j prog 0 = Znth i prog 0

def RunTime (prog cold hot cpu times : List Int) (i : Int) : Prop :=
  (∃ j, HotStart prog cpu i j ∧ Znth i times 0 = Znth (Znth i prog 0 - 1) hot 0) ∨
    ((¬ ∃ j, HotStart prog cpu i j) ∧ Znth i times 0 = Znth (Znth i prog 0 - 1) cold 0)

def RunTimes (prog cold hot cpu times : List Int) : Prop :=
  Zlength times = Zlength prog ∧ ∀ i, (0 ≤ i ∧ i < Zlength prog) → RunTime prog cold hot cpu times i

def ValidSchedule (prog cpu : List Int) : Prop := Zlength cpu = Zlength prog ∧ Forall (fun x => x = 1 ∨ x = 2) cpu

def RunCost (prog cold hot cpu : List Int) (cost : Int) : Prop :=
  ValidSchedule prog cpu ∧ ∃ times, RunTimes prog cold hot cpu times ∧ cost = times.foldr (· + ·) 0

def Pre (prog cold hot : List Int) : Prop := True

def Spec (prog cold hot : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun v => ∃ cpu, RunCost prog cold hot cpu v) (fun x => x) out

end Codeforces.examples_shard01.P073_1799D2_hot_start_up.lean
