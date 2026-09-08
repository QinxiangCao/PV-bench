import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

namespace Algorithms.kings_game.lean

open AUXLib MaxMinLib

def minister : Type := Int × Int

def mk_minister (left right : Int) : minister := (left, right)

def minister_left (p : minister) : Int := p.1

def minister_right (p : minister) : Int := p.2

def minister_product (p : minister) : Int := minister_left p * minister_right p

def default_minister : minister := mk_minister 1 1

def minister_flatten (ps : List minister) : List Int :=
  ps.flatMap (fun p => [minister_left p, minister_right p])

def FlatMinisters (flat : List Int) (ps : List minister) : Prop := flat = minister_flatten ps

def MinisterHandsBound (ps : List minister) : Prop :=
  Forall (fun p => (1 ≤ minister_left p ∧ minister_left p ≤ 10) ∧ (1 ≤ minister_right p ∧ minister_right p ≤ 10)) ps

def MinisterPermutation : List minister → List minister → Prop := List.Perm

def MinisterProductLe (p q : minister) : Prop := minister_product p ≤ minister_product q

def MinisterSorted (ps : List minister) : Prop :=
  ∀ i j, 0 ≤ i → i ≤ j → j < Zlength ps → MinisterProductLe (Znth i ps default_minister) (Znth j ps default_minister)

def PrefixLeftProduct (ps : List minister) (i : Int) : Int :=
  ((sublist 0 i ps).map minister_left).foldr (· * ·) 1

def MinisterReward (king_left : Int) (ps : List minister) (i : Int) : Int :=
  Z.div (king_left * PrefixLeftProduct ps i) (minister_right (Znth i ps default_minister))

def OrderMaxReward (king_left : Int) (ps : List minister) (reward : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun i : Int => 0 ≤ i ∧ i < Zlength ps) (fun i => MinisterReward king_left ps i) reward

def ValidOrderReward (input : List minister) (king_left : Int) (candidate : List minister × Int) : Prop :=
  MinisterPermutation input candidate.1 ∧ OrderMaxReward king_left candidate.1 candidate.2

def KingsGameOptimum (input : List minister) (king_left optimum : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (ValidOrderReward input king_left) Prod.snd optimum

def KingsGameResult (input : List minister) (king_left : Int) (output : List minister) : Prop :=
  MinisterPermutation input output ∧ MinisterSorted output ∧
    ∃ reward, OrderMaxReward king_left output reward ∧ KingsGameOptimum input king_left reward

end Algorithms.kings_game.lean
