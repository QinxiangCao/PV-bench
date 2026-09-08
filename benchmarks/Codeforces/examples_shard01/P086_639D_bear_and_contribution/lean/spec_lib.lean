import ListLib.General.Length
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Codeforces.examples_shard01.P086_639D_bear_and_contribution.lean

open AUXLib

open MaxMinLib

def RaiseCost (b c «from» target cost : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun v => exists blogs comments, blogs ≥ 0 ∧ comments ≥ 0 ∧
 target = «from» + 5 * blogs + comments ∧ v = blogs * b + comments * c) (fun x => x) cost

def ChosenBloggers (values : List Int) (k : Int) (chosen : List Int) : Prop :=
  Zlength chosen = k ∧ List.Nodup chosen ∧
  Forall (fun i => (0 ≤ i ∧ i < Zlength values) ) chosen

def TieCost (values : List Int) (k b c cost : Int) : Prop :=
  exists (chosen costs : List Int) (target : Int),
    ChosenBloggers values k chosen ∧ Zlength costs = k ∧
    (forall i, (0 ≤ i ∧ i < k) →
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) ∧
    cost = List.foldr (· + ·) 0 costs

def Pre (k b c : Int) (values : List Int) : Prop :=

  True

def Spec (k b c : Int) (values : List Int) (out : Int) : Prop := min_value_of_subset (· ≤ ·) (TieCost values k b c) (fun x => x) out

end Codeforces.examples_shard01.P086_639D_bear_and_contribution.lean
