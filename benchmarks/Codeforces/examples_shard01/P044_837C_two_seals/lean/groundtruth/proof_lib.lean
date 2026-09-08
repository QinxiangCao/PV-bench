import Codeforces.examples_shard01.P044_837C_two_seals.lean.spec_lib
import Codeforces.examples_shard01.P044_837C_two_seals.lean.helper_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Codeforces.examples_shard01.P044_837C_two_seals.lean.groundtruth.proof_lib

open Codeforces.examples_shard01.P044_837C_two_seals.lean
open scoped SimpleC

open AUXLib

private theorem best_iff (paper : Int×Int) (seals : List (Int×Int)) (i j ri rj best : Int) :
    BestBefore paper seals i j ri rj best ↔ SealAreaBefore paper seals i j ri rj best ∧
      ∀ area, SealAreaBefore paper seals i j ri rj area → area≤best := by
  constructor
  · rintro ⟨area,⟨hin,hmax⟩,he⟩
    change area=best at he
    subst area
    exact ⟨hin,hmax⟩
  · rintro ⟨hin,hmax⟩
    exact ⟨best,⟨hin,hmax⟩,rfl⟩

theorem best_before_initial__invariant_init (paper : Int×Int) (seals : List (Int×Int)) :
    BestBefore paper seals 0 1 0 0 0 := by
  apply (best_iff _ _ _ _ _ _ _).mpr
  refine ⟨Or.inl rfl,?_⟩
  rintro area (hz|⟨pi,pj,pri,prj,hb,hc⟩)
  · omega
  · unfold ChoiceBefore at hb
    rcases hc with ⟨hpi,hpj,hri,hrj,hh⟩
    omega

theorem best_before_transport__loop_transitions (paper : Int×Int) (seals : List (Int×Int))
    (i1 j1 ri1 rj1 i2 j2 ri2 rj2 best : Int)
    (he : ∀ area, SealAreaBefore paper seals i1 j1 ri1 rj1 area ↔ SealAreaBefore paper seals i2 j2 ri2 rj2 area)
    (hb : BestBefore paper seals i1 j1 ri1 rj1 best) : BestBefore paper seals i2 j2 ri2 rj2 best := by
  rcases (best_iff _ _ _ _ _ _ _).mp hb with ⟨hin,hmax⟩
  exact (best_iff _ _ _ _ _ _ _).mpr ⟨(he best).mp hin,fun a ha => hmax a ((he a).mpr ha)⟩

private theorem transport_positions (paper : Int×Int) (seals : List (Int×Int))
    (i1 j1 ri1 rj1 i2 j2 ri2 rj2 best : Int)
    (he : ∀ pi pj pri prj, (0≤pi ∧ pi<pj) → pj<Zlength seals → (0≤pri ∧ pri<2) → (0≤prj ∧ prj<2) →
      (ChoiceBefore i1 j1 ri1 rj1 pi pj pri prj ↔ ChoiceBefore i2 j2 ri2 rj2 pi pj pri prj))
    (hb : BestBefore paper seals i1 j1 ri1 rj1 best) : BestBefore paper seals i2 j2 ri2 rj2 best := by
  apply best_before_transport__loop_transitions paper seals i1 j1 ri1 rj1 i2 j2 ri2 rj2 best _ hb
  intro area
  constructor
  all_goals rintro (hz|⟨pi,pj,pri,prj,hbefore,hchoice⟩)
  · exact Or.inl hz
  · exact Or.inr ⟨pi,pj,pri,prj,(he pi pj pri prj hchoice.1 hchoice.2.1 hchoice.2.2.1 hchoice.2.2.2.1).mp hbefore,hchoice⟩
  · exact Or.inl hz
  · exact Or.inr ⟨pi,pj,pri,prj,(he pi pj pri prj hchoice.1 hchoice.2.1 hchoice.2.2.1 hchoice.2.2.2.1).mpr hbefore,hchoice⟩

theorem best_before_finish_j__loop_transitions (paper : Int×Int) (seals : List (Int×Int)) (i n best : Int)
    (hn : n=Zlength seals) (hb : BestBefore paper seals i n 0 0 best) :
    BestBefore paper seals (i+1) ((i+1)+1) 0 0 best := by
  apply transport_positions paper seals i n 0 0 (i+1) ((i+1)+1) 0 0 best _ hb
  intro pi pj pri prj hpi hpj hri hrj
  unfold ChoiceBefore
  omega

theorem best_before_finish_ri__loop_transitions (paper : Int×Int) (seals : List (Int×Int)) (i j best : Int)
    (hb : BestBefore paper seals i j 2 0 best) : BestBefore paper seals i (j+1) 0 0 best := by
  apply transport_positions paper seals i j 2 0 i (j+1) 0 0 best _ hb
  intro pi pj pri prj hpi hpj hri hrj
  unfold ChoiceBefore
  omega

theorem best_before_finish_rj__loop_transitions (paper : Int×Int) (seals : List (Int×Int)) (i j ri best : Int)
    (hb : BestBefore paper seals i j ri 2 best) : BestBefore paper seals i j (ri+1) 0 best := by
  apply transport_positions paper seals i j ri 2 i j (ri+1) 0 best _ hb
  intro pi pj pri prj hpi hpj hri hrj
  unfold ChoiceBefore
  omega

private theorem area_before_succ (paper : Int×Int) (seals : List (Int×Int)) (i j ri rj area : Int) :
    SealAreaBefore paper seals i j ri (rj+1) area ↔
      SealAreaBefore paper seals i j ri rj area ∨ SealChoice paper seals i j ri rj area := by
  constructor
  · rintro (hz|⟨pi,pj,pri,prj,hb,hc⟩)
    · exact Or.inl (Or.inl hz)
    · by_cases hold : ChoiceBefore i j ri rj pi pj pri prj
      · exact Or.inl (Or.inr ⟨pi,pj,pri,prj,hold,hc⟩)
      · have he : pi=i ∧ pj=j ∧ pri=ri ∧ prj=rj := by unfold ChoiceBefore at hb hold;omega
        rcases he with ⟨rfl,rfl,rfl,rfl⟩
        exact Or.inr hc
  · rintro ((hz|⟨pi,pj,pri,prj,hb,hc⟩)|hc)
    · exact Or.inl hz
    · exact Or.inr ⟨pi,pj,pri,prj,by unfold ChoiceBefore at hb ⊢;omega,hc⟩
    · exact Or.inr ⟨i,j,ri,rj,by unfold ChoiceBefore;omega,hc⟩

private theorem choice_area_unique (paper : Int×Int) (seals : List (Int×Int)) (i j ri rj a b : Int)
    (ha : SealChoice paper seals i j ri rj a) (hb : SealChoice paper seals i j ri rj b) : a=b :=
  ha.2.2.2.2.2.trans hb.2.2.2.2.2.symm

theorem best_before_take_current__choice_improve (paper : Int×Int) (seals : List (Int×Int)) (i j ri rj best area : Int)
    (hb : BestBefore paper seals i j ri rj best) (hc : SealChoice paper seals i j ri rj area) (hlt : best<area) :
    BestBefore paper seals i j ri (rj+1) area := by
  rcases (best_iff _ _ _ _ _ _ _).mp hb with ⟨hin,hmax⟩
  apply (best_iff _ _ _ _ _ _ _).mpr
  refine ⟨(area_before_succ _ _ _ _ _ _ _).mpr (Or.inr hc),?_⟩
  intro value hv
  rcases (area_before_succ _ _ _ _ _ _ _).mp hv with ho|hcur
  · have hh:=hmax value ho;omega
  · exact le_of_eq (choice_area_unique _ _ _ _ _ _ _ _ hcur hc)

theorem best_before_skip_dominated__choice_retain_fit (paper : Int×Int) (seals : List (Int×Int)) (i j ri rj best area : Int)
    (hb : BestBefore paper seals i j ri rj best) (hc : SealChoice paper seals i j ri rj area) (hdom : area≤best) :
    BestBefore paper seals i j ri (rj+1) best := by
  rcases (best_iff _ _ _ _ _ _ _).mp hb with ⟨hin,hmax⟩
  apply (best_iff _ _ _ _ _ _ _).mpr
  refine ⟨(area_before_succ _ _ _ _ _ _ _).mpr (Or.inl hin),?_⟩
  intro value hv
  rcases (area_before_succ _ _ _ _ _ _ _).mp hv with ho|hcur
  · exact hmax value ho
  · rw [choice_area_unique _ _ _ _ _ _ _ _ hcur hc]
    exact hdom

theorem best_before_skip_invalid__choice_retain_invalid (paper : Int×Int) (seals : List (Int×Int)) (i j ri rj best : Int)
    (hb : BestBefore paper seals i j ri rj best) (hi : ∀ area, ¬SealChoice paper seals i j ri rj area) :
    BestBefore paper seals i j ri (rj+1) best := by
  apply best_before_transport__loop_transitions paper seals i j ri rj i j ri (rj+1) best _ hb
  intro area
  rw [area_before_succ]
  exact ⟨Or.inl,fun h => h.elim id (fun hc => False.elim (hi area hc))⟩

private theorem rotation_oriented (x : Int×Int) (r : Int) : Oriented x (rotate_seal x r) := by
  unfold rotate_seal Oriented
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem orientation_rotation (x y : Int×Int) (h : Oriented x y) :
    ∃ r : Int, (0≤r ∧ r<2) ∧ rotate_seal x r=y := by
  rcases h with rfl|rfl
  · exact ⟨0,⟨by omega,by omega⟩,rfl⟩
  · exact ⟨1,⟨by omega,by omega⟩,rfl⟩

theorem best_before_complete__final_result (paper : Int×Int) (seals : List (Int×Int)) (n best : Int)
    (hn : n=Zlength seals) (hb : BestBefore paper seals n (n+1) 0 0 best) : Spec paper seals best := by
  have he : ∀ area, SealAreaBefore paper seals n (n+1) 0 0 area ↔ SealArea paper seals area := by
    intro area
    constructor
    · rintro (hz|⟨pi,pj,pri,prj,hbefore,hchoice⟩)
      · exact Or.inl hz
      · rcases hchoice with ⟨hpi,hpj,hri,hrj,hfit,ha⟩
        exact Or.inr ⟨pi,pj,rotate_seal (Znth pi seals (0,0)) pri,rotate_seal (Znth pj seals (0,0)) prj,
          hpi,hpj,rotation_oriented _ _,rotation_oriented _ _,hfit,ha⟩
    · rintro (hz|⟨pi,pj,x,y,hpi,hpj,hori,hori',hfit,ha⟩)
      · exact Or.inl hz
      · rcases orientation_rotation _ _ hori with ⟨ri,hri,hr⟩
        rcases orientation_rotation _ _ hori' with ⟨rj,hrj,hr'⟩
        refine Or.inr ⟨pi,pj,ri,rj,Or.inl (by omega),hpi,hpj,hri,hrj,?_⟩
        dsimp
        rw [hr,hr']
        exact ⟨hfit,ha⟩
  rcases (best_iff _ _ _ _ _ _ _).mp hb with ⟨hin,hmax⟩
  exact ⟨best,⟨(he best).mp hin,fun a ha => hmax a ((he a).mpr ha)⟩,rfl⟩

end Codeforces.examples_shard01.P044_837C_two_seals.lean.groundtruth.proof_lib

