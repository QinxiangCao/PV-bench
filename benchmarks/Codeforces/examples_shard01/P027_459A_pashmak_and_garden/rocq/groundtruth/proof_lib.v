Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Export PVbench.Codeforces.examples_shard01.P027_459A_pashmak_and_garden.rocq.spec_lib.

Lemma perm4_acdb__final_results : forall {A : Type} (a b c d : A),
  Permutation [a;b;c;d] [a;c;d;b].
Proof.
  intros. etransitivity.
  - apply perm_skip. apply perm_swap.
  - apply perm_skip. apply perm_skip. apply perm_swap.
Qed.
Lemma perm4_cabd__final_results : forall {A : Type} (a b c d : A),
  Permutation [a;b;c;d] [c;a;b;d].
Proof.
  intros. etransitivity.
  - apply perm_skip. apply perm_swap.
  - apply perm_swap.
Qed.
Lemma perm4_dbac__final_results : forall {A : Type} (a b c d : A),
  Permutation [a;b;c;d] [d;b;a;c].
Proof.
  intros. etransitivity.
  - apply perm_skip. apply perm_skip. apply perm_swap.
  - etransitivity.
    + apply perm_skip. apply perm_swap.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. apply perm_swap.
Qed.
Lemma perm4_bdca__final_results : forall {A : Type} (a b c d : A),
  Permutation [a;b;c;d] [b;d;c;a].
Proof.
  intros. etransitivity.
  - apply perm_swap.
  - etransitivity.
    + apply perm_skip. apply perm_skip. apply perm_swap.
    + etransitivity.
      * apply perm_skip. apply perm_swap.
      * apply perm_skip. apply perm_skip. apply perm_swap.
Qed.
Lemma perm4_bdac__final_results : forall {A : Type} (a b c d : A),
  Permutation [a;b;c;d] [b;d;a;c].
Proof.
  intros. etransitivity.
  - apply perm_swap.
  - etransitivity.
    + apply perm_skip. apply perm_skip. apply perm_swap.
    + apply perm_skip. apply perm_swap.
Qed.
Lemma perm4_badc__final_results : forall {A : Type} (a b c d : A),
  Permutation [a;b;c;d] [b;a;d;c].
Proof.
  intros. etransitivity.
  - apply perm_swap.
  - apply perm_skip. apply perm_skip. apply perm_swap.
Qed.
Lemma diagonal_abs_equal_of_corners__final_results :
  forall xl xh yl yh x1 y1 x2 y2,
    xl < xh -> yl < yh -> xh - xl = yh - yl ->
    In (x1, y1) [(xl,yl); (xl,yh); (xh,yl); (xh,yh)] ->
    In (x2, y2) [(xl,yl); (xl,yh); (xh,yl); (xh,yh)] ->
    x1 <> x2 -> y1 <> y2 ->
    Z.abs (x1 - x2) = Z.abs (y1 - y2).
Proof.
  intros xl xh yl yh x1 y1 x2 y2 Hx Hy Hside H1 H2 Hnx Hny.
  simpl in H1, H2.
  destruct H1 as [H1 | [H1 | [H1 | [H1 | []]]]];
    destruct H2 as [H2 | [H2 | [H2 | [H2 | []]]]];
    inversion H1; inversion H2; subst;
    try contradiction;
    rewrite ?Z.abs_eq, ?Z.abs_neq by lia;
    lia.
Qed.
Lemma no_completion_of_nonaxis_unequal_abs_diffs__final_results :
  forall x1 y1 x2 y2,
    x1 <> x2 -> y1 <> y2 ->
    Z.abs (x1 - x2) <> Z.abs (y1 - y2) ->
    NoCompletion x1 y1 x2 y2.
Proof.
  intros x1 y1 x2 y2 Hnx Hny Hneq.
  unfold NoCompletion, CompletesSquare, SquareCorners.
  intros (x3 & y3 & x4 & y4 & _ & xl & xh & yl & yh &
          Hx & Hy & Hside & Hperm).
  apply Hneq.
  eapply (diagonal_abs_equal_of_corners__final_results
            xl xh yl yh x1 y1 x2 y2); eauto.
  - eapply Permutation_in; [exact Hperm | simpl; auto].
  - eapply Permutation_in; [exact Hperm | simpl; auto].
Qed.
Lemma completes_square_diagonal__final_results :
  forall x1 y1 x2 y2,
    -100 <= x1 <= 100 -> -100 <= y1 <= 100 ->
    -100 <= x2 <= 100 -> -100 <= y2 <= 100 ->
    Pre x1 y1 x2 y2 -> x1 <> x2 -> y1 <> y2 ->
    Z.abs (x1 - x2) = Z.abs (y1 - y2) ->
    CompletesSquare x1 y1 x2 y2 x1 y2 x2 y1.
Proof.
  intros x1 y1 x2 y2 Hx1 Hy1 Hx2 Hy2 Hpre Hnx Hny Habs.
  destruct Hx1 as [Hx1l Hx1h]. destruct Hy1 as [Hy1l Hy1h].
  destruct Hx2 as [Hx2l Hx2h]. destruct Hy2 as [Hy2l Hy2h].
  unfold CompletesSquare. split.
  - unfold Printable. repeat constructor; lia.
  - unfold SquareCorners.
    destruct (Z_lt_ge_dec x1 x2) as [Hxx | Hxx];
      destruct (Z_lt_ge_dec y1 y2) as [Hyy | Hyy].
    + exists x1, x2, y1, y2. repeat split; try lia.
      apply perm4_acdb__final_results.
    + assert (y2 < y1) by lia.
      exists x1, x2, y2, y1. repeat split; try lia.
      apply perm4_cabd__final_results.
    + assert (x2 < x1) by lia.
      exists x2, x1, y1, y2. repeat split; try lia.
      apply perm4_dbac__final_results.
    + assert (x2 < x1) by lia. assert (y2 < y1) by lia.
      exists x2, x1, y2, y1. repeat split; try lia.
      apply perm4_bdca__final_results.
Qed.
Lemma completes_square_horizontal__final_results :
  forall x1 y1 x2 y2 d,
    -100 <= x1 <= 100 -> -100 <= y1 <= 100 ->
    -100 <= x2 <= 100 -> -100 <= y2 <= 100 ->
    Pre x1 y1 x2 y2 -> y1 = y2 -> x1 <> x2 ->
    d = Z.abs (x1 - x2) ->
    CompletesSquare x1 y1 x2 y2 x1 (y1 + d) x2 (y2 + d).
Proof.
  intros x1 y1 x2 y2 d Hx1 Hy1 Hx2 Hy2 Hpre Hy Hnx Hd. subst y2 d.
  destruct Hx1 as [Hx1l Hx1h]. destruct Hy1 as [Hy1l Hy1h].
  destruct Hx2 as [Hx2l Hx2h]. destruct Hy2 as [Hy2l Hy2h].
  assert (Hdb : 0 <= Z.abs (x1 - x2) <= 200).
  { split. apply Z.abs_nonneg. apply Z.abs_le. lia. }
  unfold CompletesSquare. split.
  - unfold Printable. repeat constructor; lia.
  - unfold SquareCorners.
    destruct (Z_lt_ge_dec x1 x2) as [Hlt | Hge].
    + exists x1, x2, y1, (y1 + Z.abs (x1 - x2)).
      split; [exact Hlt |].
      split; [rewrite Z.abs_neq by lia; lia |].
      split; [rewrite Z.abs_neq by lia; lia |].
      * apply perm_skip. apply perm_swap.
    + assert (Hlt : x2 < x1) by lia.
      exists x2, x1, y1, (y1 + Z.abs (x1 - x2)).
      split; [exact Hlt |].
      split; [rewrite Z.abs_eq by lia; lia |].
      split; [rewrite Z.abs_eq by lia; lia |].
      * apply perm4_bdac__final_results.
Qed.
Lemma completes_square_vertical__final_results :
  forall x1 y1 x2 y2 d,
    -100 <= x1 <= 100 -> -100 <= y1 <= 100 ->
    -100 <= x2 <= 100 -> -100 <= y2 <= 100 ->
    Pre x1 y1 x2 y2 -> x1 = x2 ->
    d = Z.abs (y1 - y2) ->
    CompletesSquare x1 y1 x2 y2 (x1 + d) y1 (x2 + d) y2.
Proof.
  intros x1 y1 x2 y2 d Hx1 Hy1 Hx2 Hy2 Hpre Hx Hd. subst x2 d.
  destruct Hx1 as [Hx1l Hx1h]. destruct Hy1 as [Hy1l Hy1h].
  destruct Hx2 as [Hx2l Hx2h]. destruct Hy2 as [Hy2l Hy2h].
  unfold Pre in Hpre.
  assert (Hny : y1 <> y2) by (intro; apply Hpre; auto).
  assert (Hdb : 0 <= Z.abs (y1 - y2) <= 200).
  { split. apply Z.abs_nonneg. apply Z.abs_le. lia. }
  unfold CompletesSquare. split.
  - unfold Printable. repeat constructor; lia.
  - unfold SquareCorners.
    destruct (Z_lt_ge_dec y1 y2) as [Hlt | Hge].
    + exists x1, (x1 + Z.abs (y1 - y2)), y1, y2.
      split; [rewrite Z.abs_neq by lia; lia |].
      split; [exact Hlt |].
      split; [rewrite Z.abs_neq by lia; lia |].
      * apply Permutation_refl.
    + assert (Hlt : y2 < y1) by lia.
      exists x1, (x1 + Z.abs (y1 - y2)), y2, y1.
      split; [rewrite Z.abs_eq by lia; lia |].
      split; [exact Hlt |].
      split; [rewrite Z.abs_eq by lia; lia |].
      * apply perm4_badc__final_results.
Qed.
