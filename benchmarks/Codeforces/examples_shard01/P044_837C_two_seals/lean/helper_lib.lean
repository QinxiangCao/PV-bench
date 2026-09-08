import Codeforces.examples_shard01.P044_837C_two_seals.lean.spec_lib

namespace Codeforces.examples_shard01.P044_837C_two_seals.lean

open AUXLib

open MaxMinLib

def rotate_seal (s : Int × Int) (r : Int) : Int × Int := if r = 0 then s else (s.2,s.1)

def FitsDims (w1 h1 w2 h2 a b : Int) : Prop := TwoFit a b (w1,h1) (w2,h2)

def SealChoice (paper : Int × Int) (seals : List (Int × Int)) (i j ri rj area : Int) : Prop :=
  (0 ≤ i ∧ i < j) ∧ j < Zlength seals ∧ (0 ≤ ri ∧ ri < 2) ∧ (0 ≤ rj ∧ rj < 2) ∧
    (let s1 := rotate_seal (Znth i seals (0,0)) ri
     let s2 := rotate_seal (Znth j seals (0,0)) rj
     TwoFit paper.1 paper.2 s1 s2 ∧ area = s1.1 * s1.2 + s2.1 * s2.2)

def ChoiceBefore (i j ri rj pi pj pri prj : Int) : Prop :=
  pi < i ∨ (pi = i ∧ (pj < j ∨ (pj = j ∧ (pri < ri ∨ (pri = ri ∧ prj < rj)))))

def SealAreaBefore (paper : Int × Int) (seals : List (Int × Int)) (i j ri rj area : Int) : Prop :=
  area = 0 ∨ ∃ pi pj pri prj, ChoiceBefore i j ri rj pi pj pri prj ∧ SealChoice paper seals pi pj pri prj area

def BestBefore (paper : Int × Int) (seals : List (Int × Int)) (i j ri rj best : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (SealAreaBefore paper seals i j ri rj) (fun x => x) best

end Codeforces.examples_shard01.P044_837C_two_seals.lean
