import Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_goal
import Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.Prime

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_proof_manual

open Algorithms.sieve_of_euler.lean
open scoped SimpleC

namespace ProofSupport

open AUXLib AUXLib.Prime
export AUXLib.Prime (prime prime_alt prime_ge_2)

theorem StrictPrime_two__core_invariants :
  StrictPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro d hd hv
  have := Int.le_of_dvd (by omega : (0:Int)<2) ((Z.divide_iff_dvd _ _).1 hv)
  omega

theorem EulerInitPrefix_start__core_invariants :
  ∀ (n : Int) (flags : List Int),
    Zlength flags = n - 1 →
    EulerInitPrefix n 2 flags := by
  intro n flags hlen
  exact ⟨hlen, by intro k hk; omega⟩

theorem EulerInitPrefix_step__core_invariants :
  ∀ (n i : Int) (flags : List Int),
    i <= n →
    2 <= i →
    EulerInitPrefix n i flags →
    EulerInitPrefix n (i + 1) (replace_Znth (i - 2) i flags) := by
  rintro n i flags hi h2 ⟨hlen, hpre⟩
  refine ⟨by rw [Zlength_replace_Znth]; exact hlen, ?_⟩
  intro k hk
  by_cases he : k=i
  · subst k
    exact Znth_replace_Znth_Same 0 flags (i-2) i (by omega)
  · rw [Znth_replace_Znth_Diff 0 flags (i-2) (k-2) i (by omega) (by omega) (by omega)]
    exact hpre k (by omega)

theorem EulerInitPrefix_finish_outer__core_invariants :
  ∀ (n i : Int) (flags primes : List Int),
    i > n →
    2 <= n →
    Zlength primes = n →
    EulerInitPrefix n i flags →
    EulerOuterState n 2 0 flags primes := by
  rintro n i flags primes hi hn hp ⟨hlen,hpre⟩
  refine ⟨⟨hlen, ?_⟩, hp, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro k hk
    constructor
    · intro hkle
      have he : k=2 := by omega
      subst k
      exact .inl ⟨StrictPrime_two__core_invariants, hpre 2 (by omega)⟩
    · intro hkg
      refine ⟨?_, ?_⟩
      · intro hnon
        exact False.elim (hnon (hpre k (by omega)))
      · rintro _ ⟨base,pos,hb,hbf,_⟩
        omega
  · exact ⟨by omega, by intro pos hp; omega, by intro p hp; omega, by intro p q hpq; omega⟩
  · intro pos hp
    omega

theorem prime_to_StrictPrime__core_invariants :
  ∀ p : Int,
    prime p →
    StrictPrime p := by
  intro p hp
  have hgt := prime_ge_2 p hp
  refine ⟨by omega, ?_⟩
  intro d hd hdiv
  rcases prime_divisors p hp d hdiv with h | h | h | h <;> omega

theorem StrictPrime_to_prime__core_invariants :
  ∀ p : Int,
    StrictPrime p →
    prime p := by
  rintro p ⟨hp,hdiv⟩
  apply (prime_alt p).1
  refine ⟨hp, ?_⟩
  intro d hd hv
  rcases hdiv d (by omega) hv with h | h <;> omega

theorem StrictPrime_divisor_self_or_all__core_invariants :
  ∀ p q : Int,
    StrictPrime p →
    StrictPrime q →
    Z.divide q p →
    q <= p := by
  rintro p q ⟨hp,hpdiv⟩ ⟨hq,_⟩ hdiv
  rcases hpdiv q (by omega) hdiv with h | h <;> omega

theorem EulerOuterState_nonself_first_prime_facts__core_invariants :
  ∀ (n i tot : Int) (flags primes : List Int),
    Znth (i - 2) flags 0 ≠ i →
    i <= n →
    2 <= i →
    EulerOuterState n i tot flags primes →
    1 <= tot ∧
    2 <= Znth 0 primes 0 ∧
    Znth 0 primes 0 <= i := by
  rintro n i tot flags primes hn hi h2 ⟨⟨hlen,hflag⟩,hp,hi2,hil,ht0,hti,hpre,hbounds⟩
  change FlagValue flags i ≠ i at hn
  have hc := (hflag i ⟨h2,hi⟩).1 (Int.le_refl i)
  rcases hc with ⟨_,hs⟩ | ⟨_,hl⟩
  · exact False.elim (hn hs)
  · have hq2 := hl.1.1
    have hqle := Int.le_of_dvd (by omega : 0<i) ((Z.divide_iff_dvd _ _).1 hl.2.1)
    rcases (hpre.2.2.1 (FlagValue flags i) (by omega)).1 hl.1 with ⟨pos,hpos,hpost,hval⟩
    have ht : 1≤tot := by omega
    have hb := hbounds 1 ⟨by omega,ht⟩
    have hf := hpre.2.1 1 ⟨by omega,ht⟩
    simpa using (show 1≤tot ∧ 2≤Znth (1-1) primes 0 ∧ Znth (1-1) primes 0≤i from ⟨ht,hb.1,by have := hf.2; omega⟩)

theorem PrimeBounds_from_prefix__core_invariants :
  ∀ (bound tot : Int) (primes : List Int),
    PrimePrefixList bound tot primes →
    PrimeBounds bound tot primes := by
  rintro bound tot primes ⟨_,hat,_⟩ pos hp
  have h := hat pos hp
  exact ⟨by have := h.1.1; omega,h.2⟩

theorem PrimePrefixList_extend_nonprime_current__core_invariants :
  ∀ (current tot : Int) (primes : List Int),
    PrimePrefixList (current - 1) tot primes →
    ¬ StrictPrime current →
    PrimePrefixList current tot primes := by
  rintro current tot primes ⟨h0,hat,hcomplete,hsort⟩ hn
  refine ⟨h0, ?_, ?_, hsort⟩
  · intro pos hp
    have h := hat pos hp
    exact ⟨h.1,by have := h.2; omega⟩
  · intro p hp
    by_cases he : p=current
    · subst p
      constructor
      · exact fun h => False.elim (hn h)
      · rintro ⟨pos,hlo,hhi,hval⟩
        have h := (hat pos ⟨hlo,hhi⟩).2
        omega
    · exact hcomplete p (by omega)

theorem EulerOuterState_nonself_current_not_prime__core_invariants :
  ∀ (n i tot : Int) (flags primes : List Int),
    Znth (i - 2) flags 0 ≠ i →
    i <= n →
    2 <= i →
    EulerOuterState n i tot flags primes →
    ¬ StrictPrime i := by
  intro n i tot flags primes hn hi h2 hout
  have hc := (hout.1.2 i ⟨h2,hi⟩).1 (Int.le_refl i)
  rcases hc with ⟨_,he⟩ | ⟨hnot,_⟩
  · exact False.elim (hn he)
  · exact hnot

private theorem least_nat (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  rcases h with ⟨n,hn⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m<n ∧ P m
    · rcases hm with ⟨m,hm,hp⟩
      exact ih m hm hp
    · refine ⟨n,hn,?_⟩
      intro m hp
      by_cases hmn : n≤m
      · exact hmn
      · exact False.elim (hm ⟨m,by omega,hp⟩)

theorem least_prime_factor_exists__core_invariants :
  ∀ k : Int,
    1 < k →
    ∃ q : Int, LeastPrimeFactor q k := by
  intro k hk
  have hself : Z.divide (k.toNat : Int) k := by
    refine ⟨1, ?_⟩
    simp only [Int.one_mul]
    omega
  rcases least_nat (fun n => 1<(n:Int) ∧ Z.divide (n:Int) k)
      ⟨k.toNat,by omega,hself⟩ with ⟨q,hq,hmin⟩
  refine ⟨(q:Int), ⟨hq.1,?_⟩,hq.2,?_⟩
  · intro d hd hdq
    by_cases hd1 : d=1
    · exact .inl hd1
    · have hd2 : 1<d := by omega
      have hdk : Z.divide d k := (Z.divide_iff_dvd _ _).2
        (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hdq) ((Z.divide_iff_dvd _ _).1 hq.2))
      have hqd := hmin d.toNat ⟨by omega,by simpa [Int.toNat_of_nonneg (by omega : 0≤d)] using hdk⟩
      have hdle := Int.le_of_dvd (by omega : 0<(q:Int)) ((Z.divide_iff_dvd _ _).1 hdq)
      exact .inr (by omega)
  · intro r hr hd
    have hr2 := hr.1
    have := hmin r.toNat ⟨by omega,by simpa [Int.toNat_of_nonneg (by omega : 0≤r)] using hd⟩
    omega

theorem LeastPrimeFactor_lt_of_not_prime__core_invariants :
  ∀ q k : Int,
    1 < k →
    LeastPrimeFactor q k →
    ¬ StrictPrime k →
    q < k := by
  rintro q k hk ⟨hp,hd,_⟩ hn
  have hle := Int.le_of_dvd (by omega : 0<k) ((Z.divide_iff_dvd _ _).1 hd)
  by_cases he : q=k
  · subst q; exact False.elim (hn hp)
  · omega

theorem LeastPrimeFactor_le_complement__core_invariants :
  ∀ q k b : Int,
    1 < k →
    LeastPrimeFactor q k →
    ¬ StrictPrime k →
    k = b * q →
    q <= b := by
  intro q k b hk hl hn he
  have hqlt := LeastPrimeFactor_lt_of_not_prime__core_invariants q k hk hl hn
  have hq2 := hl.1.1
  have hb : 1<b := by
    by_cases h : 1<b
    · exact h
    · have := Int.mul_le_mul_of_nonneg_right (by omega : b≤1) (by omega : 0≤q)
      simp only [Int.one_mul] at this
      omega
  rcases least_prime_factor_exists__core_invariants b hb with ⟨r,hr⟩
  have hrdk : Z.divide r k := by
    rcases hr.2.1 with ⟨a,ha⟩
    exact ⟨q*a,by grind⟩
  have hqr := hl.2.2 r hr.1 hrdk
  have hrb := Int.le_of_dvd (by omega : 0<b) ((Z.divide_iff_dvd _ _).1 hr.2.1)
  omega

theorem PrimePrefixList_lookup__core_invariants :
  ∀ (bound tot p : Int) (primes : List Int),
    PrimePrefixList bound tot primes →
    2 <= p →
    p <= bound →
    StrictPrime p →
    ∃ pos : Int,
      1 <= pos ∧ pos <= tot ∧
      Znth (pos - 1) primes 0 = p := by
  intro bound tot p primes hp h2 hle hprime
  exact (hp.2.2.1 p ⟨h2,hle⟩).1 hprime

theorem FutureSelfCompleteness_successor_prime__core_invariants :
  ∀ (frontier tot : Int) (primes : List Int),
    2 <= frontier →
    PrimePrefixList frontier tot primes →
    FutureSelfCompleteness frontier (frontier + 1) tot primes →
    StrictPrime (frontier + 1) := by
  intro frontier tot primes hf hp hfuture
  apply Classical.byContradiction
  intro hn
  rcases least_prime_factor_exists__core_invariants (frontier+1) (by omega) with ⟨q,hq⟩
  have hqlt := LeastPrimeFactor_lt_of_not_prime__core_invariants q (frontier+1) (by omega) hq hn
  have hq2 := hq.1.1
  rcases PrimePrefixList_lookup__core_invariants frontier tot q primes hp (by omega) (by omega) hq.1 with ⟨pos,hpos,hpost,hval⟩
  rcases hq.2.1 with ⟨base,hbase⟩
  have hqb := LeastPrimeFactor_le_complement__core_invariants q (frontier+1) base (by omega) hq hn hbase
  have hb2 : 2≤base := by omega
  have hblt : base<frontier := by
    have := Int.mul_le_mul_of_nonneg_left (by omega : 2≤q) (by omega : 0≤base)
    omega
  apply hfuture
  refine ⟨base,pos,hb2,hblt,hpos,hpost,by omega,?_,by rw [hval]; exact hbase⟩
  intro prev hprev hd
  have hpr := (hp.2.1 prev ⟨hprev.1,by omega⟩).1
  have hs := hp.2.2.2 prev pos ⟨hprev.1,hprev.2,hpost⟩
  have hdk : Z.divide (Znth (prev-1) primes 0) (frontier+1) := by
    rcases hd with ⟨c,hc⟩
    exact ⟨q*c,by grind⟩
  have := hq.2.2 _ hpr hdk
  omega

theorem PrimePrefixList_first_le__core_invariants :
  ∀ (bound tot pos : Int) (primes : List Int),
    PrimePrefixList bound tot primes →
    1 <= pos →
    pos <= tot →
    Znth 0 primes 0 <= Znth (pos - 1) primes 0 := by
  intro bound tot pos primes hp h1 ht
  by_cases he : pos=1
  · subst pos; simp
  · have := hp.2.2.2 1 pos ⟨by omega,by omega,ht⟩
    simpa using (Int.le_of_lt this)

theorem FutureSelfCompleteness_advance_after_product_exit__core_invariants :
  ∀ (n frontier k tot : Int) (primes : List Int),
    2 <= frontier →
    k <= n →
    frontier + 1 < k →
    PrimePrefixList frontier tot primes →
    ProductIndex frontier 1 primes > n →
    FutureSelfCompleteness frontier k tot primes →
    FutureSelfCompleteness (frontier + 1) k tot primes := by
  intro n frontier k tot primes hf hkn hkg hp hexit hold
  rintro ⟨base,pos,hb2,hbf,hpos,hpost,hprime,hprior,hprod⟩
  by_cases he : base=frontier
  · subst base
    have hle := PrimePrefixList_first_le__core_invariants frontier tot pos primes hp hpos hpost
    have hm := Int.mul_le_mul_of_nonneg_left hle (by omega : 0≤frontier)
    simp only [ProductIndex,Int.sub_self] at hexit
    omega
  · exact hold ⟨base,pos,hb2,by omega,hpos,hpost,hprime,hprior,hprod⟩

private theorem classified_successor (n current tot : Int) (flags primes : List Int)
    (hc : 2≤current) (hp : PrimePrefixList current tot primes)
    (hflag : EulerFlagState n current tot flags primes) (k : Int)
    (hk : 2≤k ∧ k≤n) (hle : k≤current+1) : FlagEntryFor k (FlagValue flags k) := by
  by_cases hkc : k≤current
  · exact (hflag.2 k hk).1 hkc
  · have he : k=current+1 := by omega
    subst k
    have hf := (hflag.2 (current+1) hk).2 (by omega)
    by_cases hs : FlagValue flags (current+1)=current+1
    · exact .inl ⟨FutureSelfCompleteness_successor_prime__core_invariants current tot primes hc hp (hf.2 hs),hs⟩
    · exact hf.1 hs

theorem EulerFlagState_advance_after_product_exit__core_invariants :
  ∀ (n frontier tot : Int) (flags primes : List Int),
    2 <= frontier →
    frontier <= n →
    PrimePrefixList frontier tot primes →
    ProductIndex frontier 1 primes > n →
    EulerFlagState n frontier tot flags primes →
    EulerFlagState n (frontier + 1) tot flags primes := by
  intro n frontier tot flags primes hf hfn hp hexit hflag
  refine ⟨hflag.1,?_⟩
  intro k hk
  refine ⟨classified_successor n frontier tot flags primes hf hp hflag k hk,?_⟩
  intro hkg
  have hfuture := (hflag.2 k hk).2 (by omega)
  exact ⟨hfuture.1,fun hs => FutureSelfCompleteness_advance_after_product_exit__core_invariants n frontier k tot primes hf hk.2 hkg hp hexit (hfuture.2 hs)⟩

theorem EulerOuterState_advance_after_product_exit__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    EulerOuterState n current tot flags primes →
    PrimePrefixList current tot primes →
    ProductIndex current 1 primes > n →
    EulerOuterState n (current + 1) tot flags primes := by
  intro n current tot flags primes hc hcn hout hp hexit
  rcases hout with ⟨hf,hlen,hc2,hcle,ht0,htlt,_,hb⟩
  exact ⟨EulerFlagState_advance_after_product_exit__core_invariants n current tot flags primes hc hcn hp hexit hf,
    hlen,by omega,by omega,ht0,by omega,by simpa using hp,hb⟩

theorem EulerOuterState_nonself_inner_start__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 ≠ current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    EulerInnerState n current 1 tot flags primes := by
  intro n current tot flags primes hn hcn hc hout
  have ht := (EulerOuterState_nonself_first_prime_facts__core_invariants n current tot flags primes hn hcn hc hout).1
  have hnot := EulerOuterState_nonself_current_not_prime__core_invariants n current tot flags primes hn hcn hc hout
  have hp := PrimePrefixList_extend_nonprime_current__core_invariants current tot primes hout.2.2.2.2.2.2.1 hnot
  rcases hout with ⟨hf,hlen,hc2,hcle,ht0,htlt,hpo,hb⟩
  refine ⟨hf,hlen,hc,hcn,by omega,ht,by omega,by omega,by omega,hp,
    PrimeBounds_from_prefix__core_invariants current tot primes hp,?_,?_,?_⟩
  · intro pos hpos; omega
  · intro pos hpos; omega
  · intro hexit
    exact EulerOuterState_advance_after_product_exit__core_invariants n current tot flags primes hc hcn
      ⟨hf,hlen,hc2,hcle,ht0,htlt,hpo,hb⟩ hp hexit

theorem EulerOuterState_self_current_prime__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 = current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    StrictPrime current := by
  intro n current tot flags primes hs hcn hc hout
  have h := (hout.1.2 current ⟨hc,hcn⟩).1 (Int.le_refl current)
  change FlagValue flags current = current at hs
  rw [hs] at h
  rcases h with ⟨hp,_⟩ | ⟨hn,hp⟩
  · exact hp
  · exact False.elim (hn hp.1)

theorem PrimePrefixList_append_current__core_invariants :
  ∀ (n current tot : Int) (primes : List Int),
    Zlength primes = n →
    tot < n →
    PrimePrefixList (current - 1) tot primes →
    StrictPrime current →
    2 <= current →
    PrimePrefixList current (tot + 1)
      (replace_Znth ((tot + 1) - 1) current primes) := by
  rintro n current tot primes hlen ht ⟨ht0,hat,hcomplete,hsort⟩ hc hc2
  have hwrite : 0≤tot+1-1 ∧ tot+1-1<Zlength primes := by omega
  have same := Znth_replace_Znth_Same 0 primes (tot+1-1) current hwrite
  have diff : ∀ pos,1≤pos → pos≤tot →
      Znth (pos-1) (replace_Znth (tot+1-1) current primes) 0 = Znth (pos-1) primes 0 := by
    intro pos hp hpt
    exact Znth_replace_Znth_Diff 0 primes (tot+1-1) (pos-1) current hwrite (by omega) (by omega)
  have hnew : ∀ pos, 1≤pos ∧ pos≤tot+1 →
      StrictPrime (Znth (pos-1) (replace_Znth (tot+1-1) current primes) 0) ∧
      Znth (pos-1) (replace_Znth (tot+1-1) current primes) 0≤current := by
    intro pos hp
    by_cases he : pos=tot+1
    · subst pos; rw [same]; exact ⟨hc,by omega⟩
    · rw [diff pos hp.1 (by omega)]
      have h := hat pos ⟨hp.1,by omega⟩
      exact ⟨h.1,by have := h.2; omega⟩
  refine ⟨by omega,hnew,?_,?_⟩
  · intro p hp
    constructor
    · intro hprime
      by_cases he : p=current
      · subst p; exact ⟨tot+1,by omega,by omega,same⟩
      · rcases (hcomplete p (by omega)).1 hprime with ⟨pos,hlo,hhi,hval⟩
        exact ⟨pos,hlo,by omega,by rw [diff pos hlo hhi]; exact hval⟩
    · rintro ⟨pos,hlo,hhi,hval⟩
      rw [←hval]
      exact (hnew pos ⟨hlo,hhi⟩).1
  · intro p q hpq
    rw [diff p hpq.1 (by omega)]
    by_cases he : q=tot+1
    · subst q; rw [same]
      have := (hat p ⟨hpq.1,by omega⟩).2
      omega
    · rw [diff q (by omega) (by omega)]
      exact hsort p q ⟨hpq.1,hpq.2.1,by omega⟩

theorem EulerFlagState_prime_append_current__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    Zlength primes = n →
    tot < n →
    EulerFlagState n current tot flags primes →
    EulerFlagState n current (tot + 1) flags
      (replace_Znth ((tot + 1) - 1) current primes) := by
  intro n current tot flags primes hc hcn hlen ht hflag
  refine ⟨hflag.1,?_⟩
  intro k hk
  refine ⟨(hflag.2 k hk).1,?_⟩
  intro hkg
  have hf := (hflag.2 k hk).2 hkg
  refine ⟨hf.1,?_⟩
  rintro hs ⟨base,pos,hb2,hbf,hpos,hpost,hpb,hprior,hprod⟩
  have ht0 : 0≤tot := by omega
  have hw : 0≤tot+1-1 ∧ tot+1-1<Zlength primes := by omega
  by_cases he : pos=tot+1
  · subst pos
    rw [Znth_replace_Znth_Same 0 primes (tot+1-1) current hw] at hpb
    omega
  · have hpt : pos≤tot := by omega
    have diff : ∀ prev,1≤prev → prev≤tot →
        Znth (prev-1) (replace_Znth (tot+1-1) current primes) 0 = Znth (prev-1) primes 0 := by
      intro prev hp hpv
      exact Znth_replace_Znth_Diff 0 primes (tot+1-1) (prev-1) current hw (by omega) (by omega)
    rw [diff pos hpos hpt] at hpb hprod
    apply hf.2 hs
    refine ⟨base,pos,hb2,hbf,hpos,hpt,hpb,?_,hprod⟩
    intro prev hprev hdiv
    apply hprior prev hprev
    rw [diff prev hprev.1 (by omega)]
    exact hdiv

theorem EulerOuterState_self_inner_start__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 = current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    EulerInnerState n current 1 (tot + 1) flags
      (replace_Znth ((tot + 1) - 1) current primes) := by
  intro n current tot flags primes hs hcn hc hout
  have hprime := EulerOuterState_self_current_prime__core_invariants n current tot flags primes hs hcn hc hout
  rcases hout with ⟨hf,hlen,hc2,hcle,ht0,htlt,hpo,hb⟩
  have hp := PrimePrefixList_append_current__core_invariants n current tot primes hlen (by omega) hpo hprime hc
  have hflag := EulerFlagState_prime_append_current__core_invariants n current tot flags primes hc hcn hlen (by omega) hf
  have hlen' : Zlength (replace_Znth (tot+1-1) current primes)=n := by rw [Zlength_replace_Znth]; exact hlen
  have hbounds := PrimeBounds_from_prefix__core_invariants current (tot+1) _ hp
  refine ⟨hflag,hlen',hc,hcn,by omega,by omega,by omega,by omega,by omega,hp,hbounds,?_,?_,?_⟩
  · intro pos hpos; omega
  · intro pos hpos; omega
  · intro hexit
    refine ⟨EulerFlagState_advance_after_product_exit__core_invariants n current (tot+1) flags _ hc hcn hp hexit hflag,
      hlen',by omega,by omega,by omega,by omega,by simpa using hp,?_⟩
    intro pos hpos
    have h := hbounds pos hpos
    exact ⟨h.1,by have := h.2; omega⟩

theorem EulerOuterState_self_first_prime_facts__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 = current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    2 <= Znth 0 (replace_Znth ((tot + 1) - 1) current primes) 0 ∧
    Znth 0 (replace_Znth ((tot + 1) - 1) current primes) 0 <= current := by
  intro n current tot flags primes hs hcn hc hout
  have hi := EulerOuterState_self_inner_start__core_invariants n current tot flags primes hs hcn hc hout
  have ht := hi.2.2.2.2.2.1
  have hb := hi.2.2.2.2.2.2.2.2.2.2.1 1 ⟨by omega,ht⟩
  simpa using hb

theorem StrictPrime_product_not_prime__core_invariants :
  ∀ a p : Int,
    2 <= a →
    StrictPrime p →
    ¬ StrictPrime (a * p) := by
  intro a p ha hp hprod
  have hp2 := hp.1
  have hmul := Int.mul_le_mul_of_nonneg_right ha (by omega : 0≤p)
  rcases hprod.2 p (by omega) ⟨a,rfl⟩ with h | h <;> omega

theorem LeastPrimeFactor_current_product__core_invariants :
  ∀ (current j tot : Int) (primes : List Int),
    2 <= current →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    PriorNonDivisibility current j primes →
    LeastPrimeFactor (Znth (j - 1) primes 0)
      (current * Znth (j - 1) primes 0) := by
  intro current j tot primes hc hj hjt hp hprior
  have hselected := (hp.2.1 j ⟨hj,hjt⟩).1
  refine ⟨hselected,⟨current,rfl⟩,?_⟩
  intro q hq hd
  rcases prime_mult q (StrictPrime_to_prime__core_invariants q hq) current (Znth (j-1) primes 0) hd with hd | hd
  · have hq2 := hq.1
    have hqle := Int.le_of_dvd (by omega : 0<current) ((Z.divide_iff_dvd _ _).1 hd)
    rcases PrimePrefixList_lookup__core_invariants current tot q primes hp (by omega) hqle hq with ⟨pos,hpos,hpost,hval⟩
    by_cases hlt : pos<j
    · exact False.elim (hprior pos ⟨hpos,hlt⟩ (by rw [hval]; exact hd))
    · by_cases he : pos=j
      · subst pos; omega
      · have hs := hp.2.2.2 j pos ⟨hj,by omega,hpost⟩
        omega
  · have hq2 := hq.1
    rcases hselected.2 q (by omega) hd with h | h <;> omega

theorem FlagEntryFor_current_product__core_invariants :
  ∀ (current j tot : Int) (primes : List Int),
    2 <= current →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    PriorNonDivisibility current j primes →
    FlagEntryFor (current * Znth (j - 1) primes 0)
      (Znth (j - 1) primes 0) := by
  intro current j tot primes hc hj hjt hp hprior
  exact .inr ⟨StrictPrime_product_not_prime__core_invariants current _ hc (hp.2.1 j ⟨hj,hjt⟩).1,
    LeastPrimeFactor_current_product__core_invariants current j tot primes hc hj hjt hp hprior⟩

theorem EulerFlagState_advance_after_inner_product_exit__core_invariants :
  ∀ (n current j tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    EulerFlagState n current tot flags primes →
    CurrentBaseProgress n current j flags primes →
    ProductIndex current j primes > n →
    EulerFlagState n (current + 1) tot flags primes := by
  intro n current j tot flags primes hc hcn hj hjt hp hf hprogress hexit
  refine ⟨hf.1,?_⟩
  intro k hk
  refine ⟨classified_successor n current tot flags primes hc hp hf k hk,?_⟩
  intro hkg
  have hfuture := (hf.2 k hk).2 (by omega)
  refine ⟨hfuture.1,?_⟩
  rintro hs ⟨base,pos,hb2,hbc,hpos,hpost,hpb,hprior,hprod⟩
  by_cases he : base=current
  · subst base
    by_cases hlt : pos<j
    · have hr : 2≤ProductIndex current pos primes ∧ ProductIndex current pos primes≤n := by
        change 2≤current*Znth (pos-1) primes 0 ∧ current*Znth (pos-1) primes 0≤n
        omega
      have hn := (hprogress pos ⟨hpos,hlt⟩ hr).2.1
      change FlagValue flags (current*Znth (pos-1) primes 0) ≠ current*Znth (pos-1) primes 0 at hn
      rw [←hprod] at hn
      exact hn hs
    · have hle : Znth (j-1) primes 0≤Znth (pos-1) primes 0 := by
        by_cases heq : pos=j
        · subst pos; omega
        · have := hp.2.2.2 j pos ⟨hj,by omega,hpost⟩
          omega
      have hm := Int.mul_le_mul_of_nonneg_left hle (by omega : 0≤current)
      unfold ProductIndex at hexit
      omega
  · exact hfuture.2 hs ⟨base,pos,hb2,by omega,hpos,hpost,hpb,hprior,hprod⟩

theorem EulerFlagState_advance_after_inner_divide__core_invariants :
  ∀ (n current j tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    EulerFlagState n current tot flags primes →
    CurrentBaseProgress n current (j + 1) flags primes →
    PriorNonDivisibility current j primes →
    Z.divide (Znth (j - 1) primes 0) current →
    EulerFlagState n (current + 1) tot flags primes := by
  intro n current j tot flags primes hc hcn hj hjt hp hf hprogress hprior hdivide
  refine ⟨hf.1,?_⟩
  intro k hk
  refine ⟨classified_successor n current tot flags primes hc hp hf k hk,?_⟩
  intro hkg
  have hfuture := (hf.2 k hk).2 (by omega)
  refine ⟨hfuture.1,?_⟩
  rintro hs ⟨base,pos,hb2,hbc,hpos,hpost,hpb,hpriorprod,hprod⟩
  by_cases he : base=current
  · subst base
    by_cases hlt : pos<j+1
    · have hr : 2≤ProductIndex current pos primes ∧ ProductIndex current pos primes≤n := by
        change 2≤current*Znth (pos-1) primes 0 ∧ current*Znth (pos-1) primes 0≤n
        omega
      have hn := (hprogress pos ⟨hpos,hlt⟩ hr).2.1
      change FlagValue flags (current*Znth (pos-1) primes 0) ≠ current*Znth (pos-1) primes 0 at hn
      rw [←hprod] at hn
      exact hn hs
    · exact hpriorprod j ⟨hj,by omega⟩ hdivide
  · exact hfuture.2 hs ⟨base,pos,hb2,by omega,hpos,hpost,hpb,hpriorprod,hprod⟩

theorem PriorNonDivisibility_nondivide_next_index__core_invariants :
  ∀ (current j tot : Int) (primes : List Int),
    2 <= current →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    PriorNonDivisibility current j primes →
    ¬ Z.divide (Znth (j - 1) primes 0) current →
    j + 1 <= tot := by
  intro current j tot primes hc hj hjt hp hprior hn
  rcases least_prime_factor_exists__core_invariants current (by omega) with ⟨q,hq⟩
  have hq2 := hq.1.1
  have hql := Int.le_of_dvd (by omega : 0<current) ((Z.divide_iff_dvd _ _).1 hq.2.1)
  rcases PrimePrefixList_lookup__core_invariants current tot q primes hp (by omega) hql hq.1 with ⟨pos,hpos,hpost,hval⟩
  by_cases hlt : pos<j
  · exact False.elim (hprior pos ⟨hpos,hlt⟩ (by rw [hval]; exact hq.2.1))
  · by_cases he : pos=j
    · subst pos
      exact False.elim (hn (by rw [hval]; exact hq.2.1))
    · omega

theorem EulerInnerState_mark_product__core_invariants :
  ∀ (n current j tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    1 <= j →
    j <= tot →
    ProductIndex current j primes <= n →
    EulerInnerState n current j tot flags primes →
    EulerInnerMarkedState n current j tot
      (replace_Znth (ProductIndex current j primes - 2)
         (Znth (j - 1) primes 0) flags)
      primes := by
  intro n current j tot flags primes hc hcn hj hjt hprodle hinner
  rcases hinner with ⟨hflag,hlen,hc2,hcle,hj2,hjle,ht0,htn,htc,hpre,hbounds,hprogress,hprior,hexitold⟩
  have hflen := hflag.1
  have hsel := hbounds j ⟨hj,hjt⟩
  let selected := Znth (j-1) primes 0
  let product := ProductIndex current j primes
  let marked := replace_Znth (product-2) selected flags
  have hs2 : 2≤selected := hsel.1
  have hpeq : product=current*selected := rfl
  have hpgt : current<product := by
    have := Int.mul_le_mul_of_nonneg_left hs2 (by omega : 0≤current)
    omega
  have hsne : selected≠product := by
    have := Int.mul_le_mul_of_nonneg_right hc (by omega : 0≤selected)
    omega
  have hprange : 2≤product ∧ product≤n := ⟨by omega,hprodle⟩
  have hwrite : 0≤product-2 ∧ product-2<Zlength flags := by omega
  have hsame : FlagValue marked product=selected := Znth_replace_Znth_Same 0 flags (product-2) selected hwrite
  have hdiff : ∀ k, 2≤k ∧ k≤n → k≠product → FlagValue marked k=FlagValue flags k := by
    intro k hk hn
    exact Znth_replace_Znth_Diff 0 flags (product-2) (k-2) selected hwrite (by omega) (by omega)
  have hentry : FlagEntryFor product selected :=
    FlagEntryFor_current_product__core_invariants current j tot primes hc hj hjt hpre hprior
  have hmarked : EulerFlagState n current tot marked primes := by
    refine ⟨?_,?_⟩
    · change Zlength (replace_Znth (product-2) selected flags)=n-1
      rw [Zlength_replace_Znth]
      exact hflen
    · intro k hk
      constructor
      · intro hkle
        rw [hdiff k hk (by omega)]
        exact (hflag.2 k hk).1 hkle
      · intro hkg
        by_cases he : k=product
        · subst k
          refine ⟨?_,?_⟩
          · intro _; rw [hsame]; exact hentry
          · intro hs
            rw [hsame] at hs
            exact False.elim (hsne hs)
        · have hfuture := (hflag.2 k hk).2 hkg
          unfold FutureFlagState
          rw [hdiff k hk he]
          exact hfuture
  have hprogressj : CurrentBaseProgress n current j marked primes := by
    intro pos hpos hr
    have hne : ProductIndex current pos primes≠product := by
      have hs := hpre.2.2.2 pos j ⟨hpos.1,hpos.2,hjt⟩
      have hm := Int.mul_lt_mul_of_pos_left hs (by omega : 0<current)
      change current*Znth (pos-1) primes 0 ≠ current*Znth (j-1) primes 0
      omega
    have h := hprogress pos hpos hr
    rw [hdiff (ProductIndex current pos primes) hr hne]
    exact h
  have hprogressnext : CurrentBaseProgress n current (j+1) marked primes := by
    intro pos hpos
    by_cases he : pos=j
    · subst pos
      intro _
      change FlagValue marked product=selected ∧ FlagValue marked product≠product ∧ FlagEntryFor product (FlagValue marked product)
      rw [hsame]
      exact ⟨rfl,hsne,hentry⟩
    · exact hprogressj pos ⟨hpos.1,by omega⟩
  have hb_n : PrimeBounds n tot primes := by
    intro pos hpos
    have h := hbounds pos hpos
    exact ⟨h.1,by have := h.2; omega⟩
  have hi : EulerInnerState n current j tot marked primes :=
    ⟨hmarked,hlen,hc,hcn,hj,hjt,ht0,htn,htc,hpre,hbounds,hprogressj,hprior,by intro h; omega⟩
  have hdivide : Z.divide selected current → EulerOuterState n (current+1) tot marked primes := by
    intro hd
    refine ⟨EulerFlagState_advance_after_inner_divide__core_invariants n current j tot marked primes hc hcn hj hjt hpre hmarked hprogressnext hprior hd,
      hlen,by omega,by omega,by omega,htc,by simpa using hpre,hb_n⟩
  have hnondivide : ¬Z.divide selected current → EulerInnerState n current (j+1) tot marked primes := by
    intro hn
    have hjnext := PriorNonDivisibility_nondivide_next_index__core_invariants current j tot primes hc hj hjt hpre hprior hn
    have hpriornext : PriorNonDivisibility current (j+1) primes := by
      intro pos hpos
      by_cases he : pos=j
      · subst pos; exact hn
      · exact hprior pos ⟨hpos.1,by omega⟩
    refine ⟨hmarked,hlen,hc,hcn,by omega,hjnext,ht0,htn,htc,hpre,hbounds,hprogressnext,hpriornext,?_⟩
    intro he
    exact ⟨EulerFlagState_advance_after_inner_product_exit__core_invariants n current (j+1) tot marked primes hc hcn (by omega) hjnext hpre hmarked hprogressnext he,
      hlen,by omega,by omega,by omega,htc,by simpa using hpre,hb_n⟩
  exact ⟨hi,hprodle,hentry,hsame,hprogressnext,hdivide,hnondivide⟩

end ProofSupport

open ProofSupport
open Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_goal

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_goal
open ProofSupport
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem product_bound (i p : Int) (hi : 0≤i) (hin : i≤46340)
    (hp : 2≤p) (hpi : p≤i) : i*p≤INT_MAX := by
  have h1 := Int.mul_le_mul_of_nonneg_left hpi hi
  have h2 := Int.mul_le_mul_of_nonneg_left hin hi
  have h3 := Int.mul_le_mul_of_nonneg_right hin (by omega : (0:Int)≤46340)
  change i*p≤2147483647
  omega

theorem proof_of_get_prime_entail_wit_1_split_goal_1 : get_prime_entail_wit_1_split_goal_1 := by
  unfold get_prime_entail_wit_1_split_goal_1
  intro n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4
  exact EulerInitPrefix_start__core_invariants n_pre flag0 PreH3

theorem proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1 := by
  unfold get_prime_entail_wit_1
  right
  intro n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_1_split_goal_1 n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4))
    | exact (proof_of_get_prime_entail_wit_1_split_goal_1 n_pre prime0 flag0 PreH1 PreH2 PreH3 PreH4)
    | trivial

theorem proof_of_get_prime_entail_wit_2_split_goal_1 : get_prime_entail_wit_2_split_goal_1 := by
  unfold get_prime_entail_wit_2_split_goal_1
  intro n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact EulerInitPrefix_step__core_invariants n_pre i flag_l_2 PreH1 PreH5 PreH7

theorem proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2 := by
  unfold get_prime_entail_wit_2
  right
  intro n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_2_split_goal_1 n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7))
    | exact (proof_of_get_prime_entail_wit_2_split_goal_1 n_pre flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7)
    | trivial

theorem proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3 := by
  unfold get_prime_entail_wit_3
  left
  intro prime_pre flag_pre n_pre prime0 flag_l_2 i tot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  subst tot
  prop_apply (naive_C_Rules.IntArray.seg_Zlength prime_pre 1 (n_pre+1) prime0)
  Intros_p hlen
  Exists flag_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact EulerInitPrefix_finish_outer__core_invariants n_pre i flag_l_2 prime0 PreH1 PreH3 (by omega) PreH7
    | omega
    | trivial

theorem proof_of_get_prime_entail_wit_5_1_split_goal_1 : get_prime_entail_wit_5_1_split_goal_1 := by
  unfold get_prime_entail_wit_5_1_split_goal_1
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
  exact product_bound i _ (by omega) (by omega) hb.1 hb.2

theorem proof_of_get_prime_entail_wit_5_1_split_goal_2 : get_prime_entail_wit_5_1_split_goal_2 := by
  unfold get_prime_entail_wit_5_1_split_goal_2
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
  exact hb.2

theorem proof_of_get_prime_entail_wit_5_1_split_goal_3 : get_prime_entail_wit_5_1_split_goal_3 := by
  unfold get_prime_entail_wit_5_1_split_goal_3
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_self_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
  exact hb.1

theorem proof_of_get_prime_entail_wit_5_1_split_goal_4 : get_prime_entail_wit_5_1_split_goal_4 := by
  unfold get_prime_entail_wit_5_1_split_goal_4
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact EulerOuterState_self_inner_start__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9

theorem proof_of_get_prime_entail_wit_5_1 : get_prime_entail_wit_5_1 := by
  unfold get_prime_entail_wit_5_1
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_1_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_1_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_get_prime_entail_wit_5_2_split_goal_1 : get_prime_entail_wit_5_2_split_goal_1 := by
  unfold get_prime_entail_wit_5_2_split_goal_1
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).2
  exact product_bound i _ (by omega) (by omega) hb.1 hb.2

theorem proof_of_get_prime_entail_wit_5_2_split_goal_2 : get_prime_entail_wit_5_2_split_goal_2 := by
  unfold get_prime_entail_wit_5_2_split_goal_2
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).2
  exact hb.2

theorem proof_of_get_prime_entail_wit_5_2_split_goal_3 : get_prime_entail_wit_5_2_split_goal_3 := by
  unfold get_prime_entail_wit_5_2_split_goal_3
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hb := (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).2
  exact hb.1

theorem proof_of_get_prime_entail_wit_5_2_split_goal_4 : get_prime_entail_wit_5_2_split_goal_4 := by
  unfold get_prime_entail_wit_5_2_split_goal_4
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact EulerOuterState_nonself_inner_start__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9

theorem proof_of_get_prime_entail_wit_5_2_split_goal_5 : get_prime_entail_wit_5_2_split_goal_5 := by
  unfold get_prime_entail_wit_5_2_split_goal_5
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact (EulerOuterState_nonself_first_prime_facts__core_invariants n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9).1

theorem proof_of_get_prime_entail_wit_5_2 : get_prime_entail_wit_5_2 := by
  unfold get_prime_entail_wit_5_2
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_2 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_3 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_4 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_5_2_split_goal_5 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_get_prime_entail_wit_5_2_split_goal_5 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_get_prime_entail_wit_7_split_goal_1 : get_prime_entail_wit_7_split_goal_1 := by
  unfold get_prime_entail_wit_7_split_goal_1
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact EulerInnerState_mark_product__core_invariants n_pre i j tot flag_l_2 prime_l_2 PreH5 PreH6 PreH9 PreH10 PreH2 PreH11

theorem proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7 := by
  unfold get_prime_entail_wit_7
  right
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_7_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
    | exact (proof_of_get_prime_entail_wit_7_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
    | trivial

theorem proof_of_get_prime_entail_wit_8_split_goal_1 : get_prime_entail_wit_8_split_goal_1 := by
  unfold get_prime_entail_wit_8_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH11.2.2.2.2.2.1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).1 PreH1)

theorem proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8 := by
  unfold get_prime_entail_wit_8
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_8_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_8_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_get_prime_entail_wit_9_split_goal_1 : get_prime_entail_wit_9_split_goal_1 := by
  unfold get_prime_entail_wit_9_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  have hle := hnext.2.2.2.2.2.1
  have hb := hnext.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega,hle⟩
  simp only [Int.add_sub_cancel] at hb
  exact product_bound i _ (by omega) (by omega) hb.1 hb.2

theorem proof_of_get_prime_entail_wit_9_split_goal_2 : get_prime_entail_wit_9_split_goal_2 := by
  unfold get_prime_entail_wit_9_split_goal_2
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  have hle := hnext.2.2.2.2.2.1
  have hb := hnext.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega,hle⟩
  simp only [Int.add_sub_cancel] at hb
  exact hb.2

theorem proof_of_get_prime_entail_wit_9_split_goal_3 : get_prime_entail_wit_9_split_goal_3 := by
  unfold get_prime_entail_wit_9_split_goal_3
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  have hle := hnext.2.2.2.2.2.1
  have hb := hnext.2.2.2.2.2.2.2.2.2.2.1 (j+1) ⟨by omega,hle⟩
  simp only [Int.add_sub_cancel] at hb
  exact hb.1

theorem proof_of_get_prime_entail_wit_9_split_goal_4 : get_prime_entail_wit_9_split_goal_4 := by
  unfold get_prime_entail_wit_9_split_goal_4
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  exact hnext

theorem proof_of_get_prime_entail_wit_9_split_goal_5 : get_prime_entail_wit_9_split_goal_5 := by
  unfold get_prime_entail_wit_9_split_goal_5
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hn : ¬Z.divide (Znth (j-1) prime_l_2 0) i := by
    intro hd
    exact PreH1 ((Z.rem_divide i (Znth (j-1) prime_l_2 0) (by omega)).2 hd)
  have hnext := PreH11.2.2.2.2.2.2 hn
  exact hnext.2.2.2.2.2.1

theorem proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9 := by
  unfold get_prime_entail_wit_9
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_4 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_4 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_9_split_goal_5 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_9_split_goal_5 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_get_prime_entail_wit_10_split_goal_1 : get_prime_entail_wit_10_split_goal_1 := by
  unfold get_prime_entail_wit_10_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa using PreH12

theorem proof_of_get_prime_entail_wit_10_split_goal_2 : get_prime_entail_wit_10_split_goal_2 := by
  unfold get_prime_entail_wit_10_split_goal_2
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa using PreH11

theorem proof_of_get_prime_entail_wit_10_split_goal_3 : get_prime_entail_wit_10_split_goal_3 := by
  unfold get_prime_entail_wit_10_split_goal_3
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simpa using PreH10

theorem proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10 := by
  unfold get_prime_entail_wit_10
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_10_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))
    | exact (proof_of_get_prime_entail_wit_10_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_10_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))
    | exact (proof_of_get_prime_entail_wit_10_split_goal_2 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_10_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))
    | exact (proof_of_get_prime_entail_wit_10_split_goal_3 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
    | trivial

theorem proof_of_get_prime_entail_wit_11_1_split_goal_1 : get_prime_entail_wit_11_1_split_goal_1 := by
  unfold get_prime_entail_wit_11_1_split_goal_1
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH10.2.2.2.2.2.2.2.2.2.2.2.2.2 PreH1

theorem proof_of_get_prime_entail_wit_11_1_split_goal_2 : get_prime_entail_wit_11_1_split_goal_2 := by
  unfold get_prime_entail_wit_11_1_split_goal_2
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH10.2.2.2.2.2.2.2.2.1

theorem proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1 := by
  unfold get_prime_entail_wit_11_1
  right
  intro n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_11_1_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_11_1_split_goal_1 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_11_1_split_goal_2 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
    | exact (proof_of_get_prime_entail_wit_11_1_split_goal_2 n_pre flag_l_2 prime_l_2 j tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
    | trivial

theorem proof_of_get_prime_entail_wit_11_2_split_goal_1 : get_prime_entail_wit_11_2_split_goal_1 := by
  unfold get_prime_entail_wit_11_2_split_goal_1
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH11.2.2.2.2.2.1

theorem proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2 := by
  unfold get_prime_entail_wit_11_2
  right
  intro n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_11_2_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
    | exact (proof_of_get_prime_entail_wit_11_2_split_goal_1 n_pre flag_l_2 prime_l_2 i tot j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
    | trivial

theorem proof_of_get_prime_entail_wit_13_split_goal_1 : get_prime_entail_wit_13_split_goal_1 := by
  unfold get_prime_entail_wit_13_split_goal_1
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have he : n_pre+1=i := by omega
  rw [he]
  exact PreH8

theorem proof_of_get_prime_entail_wit_13 : get_prime_entail_wit_13 := by
  unfold get_prime_entail_wit_13
  right
  intro n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_entail_wit_13_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8))
    | exact (proof_of_get_prime_entail_wit_13_split_goal_1 n_pre flag_l_2 prime_l_2 tot i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
    | trivial

theorem proof_of_get_prime_which_implies_wit_1_split_goal_1 : get_prime_which_implies_wit_1_split_goal_1 := by
  unfold get_prime_which_implies_wit_1_split_goal_1
  intro n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5
  rcases PreH5 with ⟨hf,hlen,hlo,hhi,ht0,htlt,hp,hb⟩
  refine ⟨hf.1,hlen,ht0,by omega,⟨hf.1,?_⟩,by simpa using hp⟩
  intro k hk
  exact (hf.2 k hk).1 (by omega)

theorem proof_of_get_prime_which_implies_wit_1 : get_prime_which_implies_wit_1 := by
  unfold get_prime_which_implies_wit_1
  right
  intro n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | Goal_apply (proof_of_get_prime_which_implies_wit_1_split_goal_1 n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5))
    | exact (proof_of_get_prime_which_implies_wit_1_split_goal_1 n_pre prime_l_2 flag_l_2 tot PreH1 PreH2 PreH3 PreH4 PreH5)
    | trivial

end Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_proof_manual
