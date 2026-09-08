import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P027_459A_pashmak_and_garden.lean

open AUXLib

inductive Answer where
  | NoSolution : Answer
  | Trees (x3 y3 x4 y4 : Int) : Answer

export Answer (NoSolution Trees)

def SquareCorners (x1 y1 x2 y2 x3 y3 x4 y4 : Int) : Prop :=
  ∃ xl xh yl yh : Int, xl < xh ∧ yl < yh ∧ xh - xl = yh - yl ∧
    Permutation [(x1,y1),(x2,y2),(x3,y3),(x4,y4)] [(xl,yl),(xl,yh),(xh,yl),(xh,yh)]

def Printable (x3 y3 x4 y4 : Int) : Prop :=
  Forall (fun v => -1000 ≤ v ∧ v ≤ 1000) [x3,y3,x4,y4]

def Pre (x1 y1 x2 y2 : Int) : Prop := ¬ (x1 = x2 ∧ y1 = y2)

def CompletesSquare (x1 y1 x2 y2 x3 y3 x4 y4 : Int) : Prop :=
  Printable x3 y3 x4 y4 ∧ SquareCorners x1 y1 x2 y2 x3 y3 x4 y4

def NoCompletion (x1 y1 x2 y2 : Int) : Prop :=
  ¬ ∃ x3 y3 x4 y4 : Int, CompletesSquare x1 y1 x2 y2 x3 y3 x4 y4

def Spec (x1 y1 x2 y2 : Int) (out : Answer) : Prop :=
  match out with
  | Trees x3 y3 x4 y4 => CompletesSquare x1 y1 x2 y2 x3 y3 x4 y4
  | NoSolution => NoCompletion x1 y1 x2 y2

end Codeforces.examples_shard01.P027_459A_pashmak_and_garden.lean
