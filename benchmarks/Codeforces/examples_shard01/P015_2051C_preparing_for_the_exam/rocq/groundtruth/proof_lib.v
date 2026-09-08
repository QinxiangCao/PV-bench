Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard01.P015_2051C_preparing_for_the_exam.rocq.spec_lib.
Require Export PVbench.Codeforces.examples_shard01.P015_2051C_preparing_for_the_exam.rocq.helper_lib.

Lemma unknown_prefix_summary_unknown_step__prefix_scan :
  forall (n : Z) (known : Z -> Prop) (q unknown only : Z),
    1 <= q <= n ->
    UnknownPrefixSummary n known q unknown only ->
    ~ known q ->
    UnknownPrefixSummary n known (q + 1) (unknown + 1) q.
Proof.
  intros n known q unknown only Hq Hsummary Hunknown.
  unfold UnknownPrefixSummary in *.
  destruct Hsummary as [Hnext Hcases].
  split; [lia |].
  destruct Hcases as [Hcase_zero | Hcases].
  - destruct Hcase_zero as [Hzero Hall].
    right; left.
    split; [lia |].
    split; [lia |].
    split; [exact Hunknown |].
    intros x Hx.
    destruct (Z.eq_dec x q) as [-> | Hxq]; [left; reflexivity |].
    right. apply Hall. lia.
  - destruct Hcases as [Hcase_one | Hcase_many].
    + destruct Hcase_one as [Hone [Honly [Honly_unknown Hall]]].
      right; right.
      split; [lia |].
      exists only, q.
      repeat split; try lia; assumption.
    + destruct Hcase_many as
          [Hmany [q1 [q2 [Hq1 [Hq2 [Hneq [Hq1_unknown Hq2_unknown]]]]]]].
      right; right.
      split; [lia |].
      exists q1, q2.
      repeat split; try lia; assumption.
Qed.
Lemma unknown_prefix_summary_known_step__prefix_scan :
  forall (n : Z) (known : Z -> Prop) (q unknown only : Z),
    1 <= q <= n ->
    UnknownPrefixSummary n known q unknown only ->
    known q ->
    UnknownPrefixSummary n known (q + 1) unknown only.
Proof.
  intros n known q unknown only Hq Hsummary Hknown.
  unfold UnknownPrefixSummary in *.
  destruct Hsummary as [Hnext Hcases].
  split; [lia |].
  destruct Hcases as [Hcase_zero | Hcases].
  - destruct Hcase_zero as [Hzero Hall].
    left.
    split; [exact Hzero |].
    intros x Hx.
    destruct (Z.eq_dec x q) as [-> | Hxq]; [exact Hknown |].
    apply Hall. lia.
  - destruct Hcases as [Hcase_one | Hcase_many].
    + destruct Hcase_one as [Hone [Honly [Honly_unknown Hall]]].
      right; left.
      split; [exact Hone |].
      split; [lia |].
      split; [exact Honly_unknown |].
      intros x Hx.
      destruct (Z.eq_dec x q) as [-> | Hxq]; [right; exact Hknown |].
      apply Hall. lia.
    + destruct Hcase_many as
          [Hmany [q1 [q2 [Hq1 [Hq2 [Hneq [Hq1_unknown Hq2_unknown]]]]]]].
      right; right.
      split; [exact Hmany |].
      exists q1, q2.
      repeat split; try lia; assumption.
Qed.
Lemma result_prefix_extend__result_steps :
  forall n missing known i out bytes result byte,
    0 <= i < Zlength missing ->
    ResultPrefix n missing known i out bytes ->
    QuestionResult n known (Znth i missing 0) result ->
    ResultDigitByte result byte ->
    ResultPrefix n missing known (i + 1)
      (app out (cons result nil)) (app bytes (cons byte nil)).
Proof.
  intros n missing known i out bytes result byte Hi Hprefix Hresult Hbyte.
  unfold ResultPrefix in *.
  destruct Hprefix as (Hout & Hbytes & Hspec & Hbridge).
  repeat split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold Spec in *.
    rewrite (sublist_split 0 (i + 1) i missing) by lia.
    rewrite (sublist_single 0 i missing) by lia.
    apply Forall2_app.
    + exact Hspec.
    + constructor; auto.
  - apply Forall2_app.
    + exact Hbridge.
    + constructor; auto.
Qed.
Lemma result_prefix_accept_only__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    unknown = 1 ->
    Znth i missing 0 = only ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 1 nil)) (app bytes (cons 49 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Honly
    Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    left. split; [reflexivity|].
    unfold CanPass.
    subst unknown.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + lia.
    + destruct Hone as (_ & _ & _ & Hall).
      intros q Hq.
      specialize (Hall q ltac:(lia)).
      rewrite Honly.
      exact Hall.
    + lia.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_accept_all_known__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    unknown = 0 ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 1 nil)) (app bytes (cons 49 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    left. split; [reflexivity|].
    unfold CanPass.
    subst unknown.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + destruct Hzero as (_ & Hall).
      intros q Hq. right. apply Hall. lia.
    + lia.
    + lia.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_reject_many_unknown__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    2 <= unknown ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 0 nil)) (app bytes (cons 48 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    right. split; [reflexivity|].
    unfold CanPass.
    intros Hpass.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + lia.
    + lia.
    + destruct Hmany as (_ & q1 & q2 & Hq1 & Hq2 & Hneq & Hnq1 & Hnq2).
      pose proof (Hpass q1 ltac:(lia)) as Hpass1.
      pose proof (Hpass q2 ltac:(lia)) as Hpass2.
      destruct Hpass1 as [Heq1 | Hknown1]; [|contradiction].
      destruct Hpass2 as [Heq2 | Hknown2]; [|contradiction].
      congruence.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_reject_other__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    unknown = 1 ->
    Znth i missing 0 <> only ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 0 nil)) (app bytes (cons 48 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Hother
    Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    right. split; [reflexivity|].
    unfold CanPass.
    intros Hpass.
    subst unknown.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + lia.
    + destruct Hone as (_ & Honly_bounds & Hnot_known & _).
      specialize (Hpass only ltac:(lia)).
      destruct Hpass as [Heq | Hknown]; [|contradiction].
      apply Hother. symmetry. exact Heq.
    + lia.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_finish__final_result :
  forall n missing known upto out bytes,
    upto = Zlength missing ->
    ResultPrefix n missing known upto out bytes ->
    Spec n missing known out /\
    ResultStringBridge out (bytes ++ (0 :: nil)).
Proof.
  intros n missing known upto out bytes Hupto Hprefix.
  subst upto.
  unfold ResultPrefix in Hprefix.
  destruct Hprefix as [Hout [Hbytes [Hspec Hdigits]]].
  split.
  - rewrite sublist_self in Hspec by reflexivity.
    exact Hspec.
  - unfold ResultStringBridge.
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + split.
      * replace (sublist 0 (Zlength out) (bytes ++ 0 :: nil)) with bytes.
        -- exact Hdigits.
        -- rewrite Hout, <- Hbytes.
           symmetry.
           apply sublist_app_exact1.
      * rewrite Hout, <- Hbytes.
        rewrite app_Znth2 by lia.
        rewrite Z.sub_diag.
        reflexivity.
Qed.
