import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Presuffix

namespace Codeforces.examples_shard01.P081_432E_square_tiling.lean

open AUXLib

-- Coq list concatenation as printed in the C annotations.
abbrev concat {A : Type} (xs : List (List A)) : List A := xs.flatten

def Cell := Int × Int

def AdjCell (p q : Cell) : Prop :=
  Z.abs (Prod.fst p - Prod.fst q) + Z.abs (Prod.snd p - Prod.snd q) = 1

def SameColorPath (g : List (List Int)) (p q : Cell) : Prop :=
  exists path : List Cell, path ≠ [] ∧ Znth 0 path (0, 0) = p ∧ Znth (Zlength path - 1) path (0, 0) = q ∧
  Forall (fun x => (0 ≤ Prod.fst x ∧ Prod.fst x < Zlength g) ∧ (0 ≤ Prod.snd x ∧ Prod.snd x < Zlength (Znth 0 g [])) ∧
    Znth (Prod.snd x) (Znth (Prod.fst x) g []) 0 = Znth (Prod.snd p) (Znth (Prod.fst p) g []) 0) path ∧
  forall i, (0 ≤ i ∧ i < Zlength path - 1) → AdjCell (Znth i path (0, 0)) (Znth (i + 1) path (0, 0))

def SquareTiling (n m : Int) (g : List (List Int)) : Prop :=
  (Zlength g = n ∧ Forall (fun row => Zlength row = m) g) ∧ Forall (Forall (fun c => (65 ≤ c ∧ c ≤ 90) )) g ∧
  forall p, (0 ≤ Prod.fst p ∧ Prod.fst p < n) → (0 ≤ Prod.snd p ∧ Prod.snd p < m) → exists r c side,
    side ≥ 1 ∧ (r ≤ Prod.fst p ∧ Prod.fst p < r + side) ∧ (c ≤ Prod.snd p ∧ Prod.snd p < c + side) ∧ r ≥ 0 ∧ c ≥ 0 ∧ r + side ≤ n ∧ c + side ≤ m ∧
    forall q, (0 ≤ Prod.fst q ∧ Prod.fst q < n) → (0 ≤ Prod.snd q ∧ Prod.snd q < m) →
      (SameColorPath g p q ↔ (r ≤ Prod.fst q ∧ Prod.fst q < r + side) ∧ (c ≤ Prod.snd q ∧ Prod.snd q < c + side) )

def Flatten (g : List (List Int)) : List Int := List.flatten g

def Pre (n m : Int) : Prop :=

  True

def Spec (n m : Int) (out : List (List Int)) : Prop :=
  SquareTiling n m out ∧ forall q, SquareTiling n m q → ((Flatten out) = (Flatten q) ∨ ((exists i, (0 ≤ i ∧ i < min (Zlength (Flatten out)) (Zlength (Flatten q))) ∧
    (forall j, (0 ≤ j ∧ j < i) → Znth j (Flatten out) 0 = Znth j (Flatten q) 0) ∧
    Znth i (Flatten out) 0 < Znth i (Flatten q) 0) ∨
  (Zlength (Flatten out) < Zlength (Flatten q) ∧ ListLib.is_prefix (Flatten out) (Flatten q))))

end Codeforces.examples_shard01.P081_432E_square_tiling.lean
