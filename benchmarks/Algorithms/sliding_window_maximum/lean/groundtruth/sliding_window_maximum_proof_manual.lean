import Algorithms.sliding_window_maximum.lean.groundtruth.sliding_window_maximum_goal
import Algorithms.sliding_window_maximum.lean.groundtruth.sliding_window_maximum_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.sliding_window_maximum.lean.groundtruth.sliding_window_maximum_proof_manual

open Algorithms.sliding_window_maximum.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib

theorem replace_Znth_append_bounds__value_loop_exit_and_append
    (q_l : List Int) (head tail i n : Int) (hlen : Zlength q_l = n)
    (hht : 0 ≤ head ∧ head ≤ tail) (hit : tail ≤ i ∧ i < n)
    (hold : ∀ pos, (head ≤ pos ∧ pos < tail) → 0 ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < n)
    (pos : Int) (hpos : head ≤ pos ∧ pos < tail+1) :
    0 ≤ Znth pos (replace_Znth tail i q_l) 0 ∧ Znth pos (replace_Znth tail i q_l) 0 < n := by
  by_cases heq : pos = tail
  · subst pos
    rw [Znth_replace_Znth_Same 0 q_l tail i (by omega)]
    omega
  · rw [Znth_replace_Znth_Diff 0 q_l tail pos i (by omega) (by omega) (by omega)]
    exact hold pos (by omega)

theorem queue_append_state__value_loop_exit_and_append
    (l q_l : List Int) (head tail i k : Int) (hlen : Zlength l = Zlength q_l)
    (hk : 1 ≤ k) (hi : 0 ≤ i ∧ i < Zlength l) (hht : 0 ≤ head ∧ head ≤ tail) (hti : tail ≤ i)
    (hstate : SWMQueuePendingState l q_l head tail i k)
    (hlast : head < tail → Znth (Znth (tail-1) q_l 0) l 0 > Znth i l 0) :
    SWMQueueState l (replace_Znth tail i q_l) head (tail+1) (i+1) k := by
  rcases hstate with ⟨he, hinc, hdec, hcov⟩
  have hs := Znth_replace_Znth_Same 0 q_l tail i (by omega)
  have hd (p : Int) (hp : head ≤ p ∧ p < tail) :
      Znth p (replace_Znth tail i q_l) 0 = Znth p q_l 0 :=
    Znth_replace_Znth_Diff 0 q_l tail p i (by omega) (by omega) (by omega)
  have hnewEntries : SWMQueueEntriesInWindow (replace_Znth tail i q_l) head (tail+1) (i+1-k) (i+1) := by
    intro p hp
    by_cases hpt : p = tail
    · subst p; rw [hs] <;> omega
    · rw [hd p (by omega)]
      have := he p (by omega)
      omega
  have hnewDec : SWMQueueValueDecreasing l (replace_Znth tail i q_l) head (tail+1) := by
    intro p q hpq
    by_cases hqt : q = tail
    · subst q
      rw [hs, hd p (by omega)]
      by_cases hpt : p = tail-1
      · subst p; exact hlast (by omega)
      · have := hdec p (tail-1) (by omega)
        have := hlast (by omega)
        omega
    · rw [hd p (by omega), hd q (by omega)]
      exact hdec p q (by omega)
  have hnewCov : SWMQueueCoversWindow l (replace_Znth tail i q_l) head (tail+1) (i+1-k) (i+1) := by
    intro idx hidx hwin
    by_cases heq : idx = i
    · subst idx
      exact ⟨tail, by omega, by rw [hs] <;> omega, by rw [hs] <;> omega⟩
    · rcases hcov idx hidx (by omega) with ⟨p, hp, hip, hv⟩ | hv
      · exact ⟨p, by omega, by rw [hd p hp] <;> omega, by rw [hd p hp]; exact hv⟩
      · exact ⟨tail, by omega, by rw [hs] <;> omega, by rw [hs]; exact hv⟩
  refine ⟨hnewEntries, ?_, hnewDec, hnewCov, ?_⟩
  · intro p q hpq
    by_cases hqt : q = tail
    · subst q
      rw [hs, hd p (by omega)]
      exact (he p (by omega)).2
    · rw [hd p (by omega), hd q (by omega)]
      exact hinc p q (by omega)
  · intro hnonempty
    refine ⟨Znth head (replace_Znth tail i q_l) 0, hnewEntries head (by omega), rfl, ?_⟩
    intro idx hidx
    rcases hnewCov idx (by omega) hidx with ⟨p, hp, hip, hv⟩
    by_cases heq : p = head
    · subst p; exact hv
    · have := hnewDec head p (by omega)
      omega

theorem queue_append_storage__value_loop_exit_and_append
    (l q_l : List Int) (head tail i : Int) (hlen : Zlength q_l = Zlength l)
    (hi : 0 ≤ i ∧ i < Zlength l) (hht : 0 ≤ head ∧ head ≤ tail) (hti : tail ≤ i)
    (hb : ∀ pos, (head ≤ pos ∧ pos < tail) → 0 ≤ Znth pos q_l 0 ∧ Znth pos q_l 0 < Zlength l) :
    SWMQueueStorageSafe l (replace_Znth tail i q_l) head (tail+1) (i+1) := by
  refine ⟨?_, by omega, by omega, by omega, ?_⟩
  · rw [Zlength_replace_Znth]; exact hlen
  · exact replace_Znth_append_bounds__value_loop_exit_and_append q_l head tail i (Zlength l) hlen hht (by omega) hb

private theorem getD_append_left (l1 l2 : List Int) (d : Int) (n : Nat) (hn : n < l1.length) :
    (l1 ++ l2).getD n d = l1.getD n d := by
  induction l1 generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n (by simpa using hn)

theorem Znth_app_left__window_output_append (l1 l2 : List Int) (d i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1++l2) d = Znth i l1 d := by
  unfold Znth
  exact getD_append_left l1 l2 d i.toNat (by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega)

theorem Znth_app_last__window_output_append (l : List Int) (d x : Int) :
    Znth (Zlength l) (l++[x]) d = x := by
  rw [app_Znth2 d l [x] (Zlength l) (by omega)]
  simp [Znth]

theorem SWMOutputPrefix_app_single__window_output_append
    (l : List Int) (k out_idx : Int) (out : List Int) (value : Int)
    (hshape : SWMOutputPrefixShape l k out_idx out) (hp : SWMOutputPrefix l k out_idx out)
    (hv : WindowMaxValue l out_idx (out_idx+k) value) :
    SWMOutputPrefix l k (out_idx+1) (out++[value]) := by
  intro idx hi
  by_cases hlt : idx < out_idx
  · rw [Znth_app_left__window_output_append out [value] 0 idx (by have := hshape.2.2.2; omega)]
    exact hp idx (by omega)
  · have heq : idx = out_idx := by omega
    subst idx
    have hz : Znth out_idx (out++[value]) 0 = value := by
      rw [← hshape.2.2.2]; exact Znth_app_last__window_output_append out 0 value
    rw [hz]; exact hv

theorem SWMOutputPrefixShape_app_single__window_output_append
    (l : List Int) (k out_idx : Int) (out : List Int) (value : Int)
    (hshape : SWMOutputPrefixShape l k out_idx out) (hr : out_idx < Zlength l-k+1) :
    SWMOutputPrefixShape l k (out_idx+1) (out++[value]) := by
  rcases hshape with ⟨hk, hkl, hi, hlen⟩
  refine ⟨hk, hkl, by omega, ?_⟩
  simpa [Zlength, List.length_append, Int.natCast_add] using congrArg (fun x : Int => x+1) hlen

theorem drop_loop_remove_expired_head__head_drop_transitions
    (l q_l : List Int) (head tail i k : Int) (hn : head < tail) (hex : Znth head q_l 0 ≤ i-k)
    (hstate : SWMQueueDropLoopState l q_l head tail i k) :
    SWMQueueDropLoopState l q_l (head+1) tail i k := by
  rcases hstate with ⟨he, hi, hv, hc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pos hp; exact he pos (by omega)
  · intro p q hpq; exact hi p q (by omega)
  · intro p q hpq; exact hv p q (by omega)
  · intro idx hidx hw
    rcases hc idx hidx hw with ⟨p, hp, hip, hval⟩
    by_cases heq : p = head
    · subst p; omega
    · exact ⟨p, by omega, hip, hval⟩

theorem drop_loop_exit_nonexpired__head_drop_transitions
    (l q_l : List Int) (head tail i k : Int) (hn : head < tail) (hh : i-k < Znth head q_l 0)
    (hstate : SWMQueueDropLoopState l q_l head tail i k) :
    SWMQueueAfterDrop l q_l head tail i k := by
  rcases hstate with ⟨he, hi, hv, hc⟩
  refine ⟨?_, hi, hv, hc⟩
  intro pos hp
  have hep := he pos hp
  by_cases heq : pos = head
  · subst pos; omega
  · have := hi head pos (by omega)
    omega

theorem SWMQueuePendingState_drop_tail__pending_and_tail_drop
    (l q_l : List Int) (head tail i k : Int) (hn : head < tail)
    (hd : Znth (Znth (tail-1) q_l 0) l 0 ≤ Znth i l 0)
    (hstate : SWMQueuePendingState l q_l head tail i k) :
    SWMQueuePendingState l q_l head (tail-1) i k := by
  rcases hstate with ⟨he, hi, hv, hc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pos hp; exact he pos (by omega)
  · intro p q hpq; exact hi p q (by omega)
  · intro p q hpq; exact hv p q (by omega)
  · intro idx hidx hw
    rcases hc idx hidx hw with ⟨p, hp, hip, hval⟩ | hpend
    · by_cases hlt : p < tail-1
      · exact Or.inl ⟨p, by omega, hip, hval⟩
      · have heq : p = tail-1 := by omega
        subst p
        exact Or.inr (by omega)
    · exact Or.inr hpend

end ProofSupport

open ProofSupport
open Algorithms.sliding_window_maximum.lean.groundtruth.sliding_window_maximum_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.sliding_window_maximum.lean.groundtruth.sliding_window_maximum_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 : maxSlidingWindow_entail_wit_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_1
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro pos hp
  omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 : maxSlidingWindow_entail_wit_1_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_2
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pos hp; omega
  · intro p q hpq; omega
  · intro p q hpq; omega
  · intro idx hidx hw; omega
  · intro h; omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 : maxSlidingWindow_entail_wit_1_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_3
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro pos hp
  omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 : maxSlidingWindow_entail_wit_1_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_4
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro idx hidx
  omega

theorem proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 : maxSlidingWindow_entail_wit_1_split_goal_5 := by
  unfold maxSlidingWindow_entail_wit_1_split_goal_5
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact ⟨PreH1, by omega, by omega, rfl⟩

-- Keep the generated residual branch and real SL preprocessing. Goal_apply
-- needs explicit arguments and pure-context extraction; forall conclusions
-- additionally use direct application when its parameter matcher cannot close them.
theorem proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1 := by
  unfold maxSlidingWindow_entail_wit_1
  right
  intro k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
    | exact (proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 k_pre n_pre q0 l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 : maxSlidingWindow_entail_wit_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_2_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 : maxSlidingWindow_entail_wit_2_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_2_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  refine ⟨PreH21.1, PreH21.2.1, PreH21.2.2.1, ?_⟩
  intro idx hidx hw
  exact PreH21.2.2.2.1 idx hidx (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2 := by
  unfold maxSlidingWindow_entail_wit_2
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 : maxSlidingWindow_entail_wit_3_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_3_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact drop_loop_remove_expired_head__head_drop_transitions l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 : maxSlidingWindow_entail_wit_3_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_3_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rcases PreH20 with ⟨hlen, hp, hb, ht, he⟩
  refine ⟨hlen, hp, by omega, ht, ?_⟩
  intro pos hpos
  exact he pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3 := by
  unfold maxSlidingWindow_entail_wit_3
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 : maxSlidingWindow_entail_wit_4_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_4_1_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 : maxSlidingWindow_entail_wit_4_1_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_4_1_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  refine ⟨?_, PreH20.2.1, PreH20.2.2.1, PreH20.2.2.2⟩
  intro pos hpos
  omega

theorem proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1 := by
  unfold maxSlidingWindow_entail_wit_4_1
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 : maxSlidingWindow_entail_wit_4_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_4_2_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 : maxSlidingWindow_entail_wit_4_2_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_4_2_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact drop_loop_exit_nonexpired__head_drop_transitions l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2 := by
  unfold maxSlidingWindow_entail_wit_4_2
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 : maxSlidingWindow_entail_wit_5_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH20

theorem proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 : maxSlidingWindow_entail_wit_5_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_5_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  refine ⟨PreH19.1, PreH19.2.1, PreH19.2.2.1, ?_⟩
  intro idx hidx hw
  exact Or.inl (PreH19.2.2.2 idx hidx hw)

theorem proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5 := by
  unfold maxSlidingWindow_entail_wit_5
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 : maxSlidingWindow_entail_wit_6_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_6_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact SWMQueuePendingState_drop_tail__pending_and_tail_drop l q_l_2 head tail i k_pre PreH2 PreH1 PreH21

theorem proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 : maxSlidingWindow_entail_wit_6_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_6_split_goal_2
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rcases PreH20 with ⟨hlen, hp, hb, ht, he⟩
  refine ⟨hlen, hp, by omega, by omega, ?_⟩
  intro pos hpos
  exact he pos (by omega)

theorem proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6 := by
  unfold maxSlidingWindow_entail_wit_6
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)

theorem proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 : maxSlidingWindow_entail_wit_7_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_7_1_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1 := by
  unfold maxSlidingWindow_entail_wit_7_1
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 : maxSlidingWindow_entail_wit_7_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_7_2_split_goal_1
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2 := by
  unfold maxSlidingWindow_entail_wit_7_2
  right
  intro k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 : maxSlidingWindow_entail_wit_8_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact replace_Znth_append_bounds__value_loop_exit_and_append q_l_2 head tail i n_pre
    PreH5 ⟨PreH8, PreH9⟩ ⟨PreH10, PreH7⟩ PreH20

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 : maxSlidingWindow_entail_wit_8_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact queue_append_state__value_loop_exit_and_append l q_l_2 head tail i k_pre
    (by omega) PreH1 (by omega) ⟨PreH8, PreH9⟩ PreH10 PreH19 PreH22

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 : maxSlidingWindow_entail_wit_8_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_3
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply queue_append_storage__value_loop_exit_and_append l q_l_2 head tail i
  · omega
  · omega
  · exact ⟨PreH8, PreH9⟩
  · exact PreH10
  · intro pos hp
    rw [PreH4]
    exact PreH20 pos hp

theorem proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 : maxSlidingWindow_entail_wit_8_split_goal_4 := by
  unfold maxSlidingWindow_entail_wit_8_split_goal_4
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [Zlength_replace_Znth]; exact PreH5

theorem proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8 := by
  unfold maxSlidingWindow_entail_wit_8
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | exact (proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 : maxSlidingWindow_entail_wit_9_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have h := PreH20.2.2.2.2 (show head < tail ∧ k_pre ≤ i+1 by omega)
  rw [show i-k_pre+1 = i+1-k_pre by omega]
  exact h

theorem proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 : maxSlidingWindow_entail_wit_9_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_9_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9 := by
  unfold maxSlidingWindow_entail_wit_9
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 : maxSlidingWindow_entail_wit_10_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_10_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH22

theorem proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 : maxSlidingWindow_entail_wit_10_split_goal_2 := by
  unfold maxSlidingWindow_entail_wit_10_split_goal_2
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rw [← PreH14]
  apply SWMOutputPrefix_app_single__window_output_append l k_pre out_idx out_l_2 _ PreH18 PreH19
  rw [PreH14, show i-k_pre+1+k_pre = i+1 by omega]
  exact PreH23

theorem proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 : maxSlidingWindow_entail_wit_10_split_goal_3 := by
  unfold maxSlidingWindow_entail_wit_10_split_goal_3
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rw [← PreH14]
  apply SWMOutputPrefixShape_app_single__window_output_append l k_pre out_idx out_l_2 _ PreH18
  omega

theorem proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10 := by
  unfold maxSlidingWindow_entail_wit_10
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
    | exact (proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)

theorem proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 : maxSlidingWindow_entail_wit_11_1_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_11_1_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact PreH19

theorem proof_of_maxSlidingWindow_entail_wit_11_1 : maxSlidingWindow_entail_wit_11_1 := by
  unfold maxSlidingWindow_entail_wit_11_1
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | exact (proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 : maxSlidingWindow_entail_wit_11_2_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_11_2_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_11_2 : maxSlidingWindow_entail_wit_11_2 := by
  unfold maxSlidingWindow_entail_wit_11_2
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 : maxSlidingWindow_entail_wit_12_split_goal_1 := by
  unfold maxSlidingWindow_entail_wit_12_split_goal_1
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH21

theorem proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12 := by
  unfold maxSlidingWindow_entail_wit_12
  right
  intro k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | Goal_apply (proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)
    | exact (proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 k_pre n_pre l out_l_2 q_l_2 i head tail out_idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13 := by
  unfold maxSlidingWindow_entail_wit_13
  right
  intro out_pre k_pre n_pre l out_l_2 out_idx tail head i q_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hi : i = n_pre := by omega
  have ho : out_idx = n_pre-k_pre+1 := by have := PreH15 (by omega); omega
  have hresult : SlidingWindowMaximum l k_pre out_l_2 := by
    have hlen := PreH18.2.2.2
    refine ⟨by omega, ?_⟩
    intro idx hidx
    exact PreH19 idx (by omega)
  rw [ho]
  Exists out_l_2
  split_pure_spatial
  · sep_apply (naive_C_Rules.IntArray.seg_to_full out_pre 0 (n_pre-k_pre+1) out_l_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega

end Algorithms.sliding_window_maximum.lean.groundtruth.sliding_window_maximum_proof_manual
