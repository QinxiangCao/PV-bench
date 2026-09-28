Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.Logic.ClassicalEpsilon.

Require Export PVbench.Codeforces.examples_shard00.P025_1207B_square_filling.rocq.helper_lib.

Lemma ScanOperations_empty__initialization : forall n m a,
  ScanOperations n m a 0 0 nil.
Proof.
intros n m a.
unfold ScanOperations.
split.
- constructor.
- split.
+ constructor.
+ intros row col Hrow Hcol.
split.
* intros Hin.
inversion Hin.
* intros [Hbefore _].
unfold BeforeSquare in Hbefore.
lia.
Qed.

Lemma made_state_nil__initialization :
  made_state nil = repeat 0 2500.
Proof.
assert (Hcell : forall k, made_cell nil k = 0).
{
    intros k.
unfold made_cell.
destruct excluded_middle_informative as [Hcovered | Hnotcovered].
- unfold CellCovered in Hcovered.
destruct Hcovered as (x & y & Hin & _).
inversion Hin.
- reflexivity.
}
  assert (Hmap : forall l : list nat,
    map (made_cell nil) l = repeat 0 (length l)).
{
    intros l.
induction l as [| k ks IH].
- reflexivity.
- simpl.
rewrite Hcell, IH.
reflexivity.
}
  unfold made_state.
rewrite Hmap, length_seq.
reflexivity.
Qed.

Lemma staged_ops_nil__initialization :
  staged_ops nil = repeat None 5000.
Proof.
unfold staged_ops, operation_words, Zlength.
reflexivity.
Qed.

Lemma ScanOperations_row_advance__operation_scan_boundaries :
  forall n m a i j ops,
    ScanOperations n m a i j ops ->
    0 <= j <= m - 1 ->
    j + 1 >= m ->
    ScanOperations n m a (i + 1) 0 ops.
Proof.
intros n m a i j ops Hscan Hj Hguard.
unfold ScanOperations in Hscan |- *.
destruct Hscan as [Hnodup [Hbounds Hscan]].
split; [exact Hnodup |].
split; [exact Hbounds |].
intros row0 col0 Hrow Hcol.
specialize (Hscan row0 col0 Hrow Hcol).
assert (j = m - 1) by lia.
subst j.
rewrite Hscan.
unfold BeforeSquare.
split.
- intros [[Hbefore | [Hsame Hcol_before]] Hall].
+ split; [left; lia | exact Hall].
+ split; [left; lia | exact Hall].
- intros [[Hbefore | [Hsame Hcol_before]] Hall].
+ split.
* assert (row0 < i \/ row0 = i) as [Hlt | Heq] by lia.
-- left; exact Hlt.
-- right; split; [exact Heq | lia].
* exact Hall.
+ lia.
Qed.

Lemma ScanOperations_skip_square__square_decision_transition :
  forall n m a i j ops,
    0 <= i < n - 1 -> 0 <= j < m - 1 ->
    ScanOperations n m a i j ops ->
    ~ SquareAllOn a i j ->
    ScanOperations n m a i (j + 1) ops.
Proof.
intros n m a i j ops Hi Hj [Hnodup [Hbounds Hscan]] Hnot.
split; [exact Hnodup|].
split; [exact Hbounds|].
intros row col Hrow Hcol.
rewrite Hscan by assumption.
unfold BeforeSquare.
split.
- intros [Hbefore Hsquare].
split; [|exact Hsquare].
destruct Hbefore as [Hlt | [Heq Hlt]]; [auto|right; split; lia].
- intros [Hbefore Hsquare].
split; [|exact Hsquare].
destruct Hbefore as [Hlt | [Heq Hlt]].
+ auto.
+ right.
split; [exact Heq|].
assert (col <> j).
{ intro Heqcol.
subst row col.
contradiction.
}
      lia.
Qed.

Lemma ScanOperations_add_square__square_decision_transition :
  forall n m a i j ops,
    0 <= i < n - 1 -> 0 <= j < m - 1 ->
    ScanOperations n m a i j ops ->
    SquareAllOn a i j ->
    ScanOperations n m a i (j + 1) (ops ++ cons (i, j) nil).
Proof.
intros n m a i j ops Hi Hj [Hnodup [Hbounds Hscan]] Hall.
assert (Hfresh : ~ In (i, j) ops).
{ intro Hin.
apply Hscan in Hin; [|lia|lia].
destruct Hin as [Hbefore _].
unfold BeforeSquare in Hbefore.
lia.
}
  split.
- apply NoDup_app.
+ exact Hnodup.
+ repeat constructor; simpl; auto.
+ intros p Hinp Hinone.
simpl in Hinone.
destruct Hinone as [Heq | []].
subst p.
exact (Hfresh Hinp).
- split.
+ apply Forall_app.
split; [exact Hbounds|].
repeat constructor; simpl; lia.
+ intros row col Hrow Hcol.
rewrite in_app_iff.
simpl.
rewrite Hscan by assumption.
unfold BeforeSquare.
split.
* intros [[Hbefore Hsquare] | [Heq | []]].
-- split; [|exact Hsquare].
destruct Hbefore as [Hlt | [Herow Hlt]].
++ auto.
++ right.
split; [exact Herow|lia].
-- inversion Heq.
subst row col.
split; [right; split; lia|exact Hall].
* intros [Hbefore Hsquare].
destruct Hbefore as [Hlt | [Herow Hlt]].
-- left.
split; [left; exact Hlt|exact Hsquare].
-- destruct (Z.eq_dec col j) as [Heqcol | Hne].
++ right.
left.
f_equal; lia.
++ left.
split; [right; split; [exact Herow|lia]|exact Hsquare].
Qed.

Lemma staged_ops_snoc__square_decision_transition :
  forall ops i j count,
    count = Zlength ops ->
    0 <= 2 * count ->
    2 * count + 1 < 5000 ->
    replace_Znth (2 * count + 1) (Some (j + 1))
      (replace_Znth (2 * count) (Some (i + 1)) (staged_ops ops)) =
    staged_ops (ops ++ cons (i, j) nil).
Proof.
intros ops i j count Hcount.
assert (Hwords : Zlength (operation_words ops) = 2 * count).
{ subst count.
unfold operation_words.
induction ops as [|[x y] tl IH].
- reflexivity.
- simpl flat_map.
rewrite Zlength_cons, Zlength_cons, Zlength_cons, IH.
lia.
}
  intros Hlo Hhi.
unfold staged_ops at 1 2.
rewrite replace_Znth_app_r by (rewrite Hwords; lia).
rewrite (replace_Znth_nothing (2 * count) (operation_words ops)
    (Some (i + 1))) by (rewrite Hwords; lia).
rewrite Hwords.
rewrite replace_Znth_app_r by (rewrite Hwords; lia).
rewrite (replace_Znth_nothing (2 * count + 1) (operation_words ops)
    (Some (j + 1))) by (rewrite Hwords; lia).
replace (2 * count + 1 - 2 * count) with 1 by lia.
replace (2 * count - 2 * count) with 0 by lia.
assert (Hk : 2 <= Z.of_nat (Z.to_nat (5000 - 2 * count))).
{ rewrite Z2Nat.id by lia.
lia.
}
  assert (Hnat :
    Z.to_nat (5000 - 2 * count - 2) =
    (Z.to_nat (5000 - 2 * count) - 2)%nat).
{ rewrite Z2Nat.inj_sub by lia.
reflexivity.
}
  assert (Hnat' :
    Z.to_nat (5000 - (2 * count + 2)) =
    (Z.to_nat (5000 - 2 * count) - 2)%nat).
{ replace (5000 - (2 * count + 2)) with (5000 - 2 * count - 2) by lia.
exact Hnat.
}
  destruct (Z.to_nat (5000 - 2 * count)) as [|[|k]] eqn:Ek;
    simpl in Hk; try lia.
cbn [replace_Znth replace_nth].
unfold operation_words.
assert (How : Zlength
    (flat_map
      (fun p : Z * Z =>
        cons (Some (fst p + 1)) (cons (Some (snd p + 1)) nil)) ops) =
    2 * count).
{ exact Hwords.
}
  rewrite flat_map_app.
cbn [flat_map].
rewrite Zlength_app, How.
replace (2 * count + 1 - 2 * count) with 1 by lia.
cbn [replace_Znth replace_nth].
replace (Zlength (cons (Some (i + 1)) (cons (Some (j + 1)) nil) ++ nil)) with 2
    by reflexivity.
cbn [replace_Znth replace_nth fst snd].
replace (Zlength (cons (Some (i + 1)) (cons (Some (j + 1)) nil) ++ nil)) with 2
    by reflexivity.
rewrite Hnat'.
simpl.
unfold replace_Znth.
simpl.
rewrite <- app_assoc.
replace (k - 0)%nat with k by lia.
reflexivity.
Qed.

Lemma flat_coord__square_decision_transition :
  forall row col,
    0 <= col < 50 ->
    (row * 50 + col) / 50 = row /\
    (row * 50 + col) mod 50 = col.
Proof.
intros row col Hcol.
replace (row * 50 + col) with (col + row * 50) by ring.
rewrite Z.div_add by lia.
rewrite Z.mod_add by lia.
rewrite Z.div_small by lia.
rewrite Z.mod_small by lia.
lia.
Qed.

Lemma CellCovered_snoc__square_decision_transition :
  forall ops i j row col,
    CellCovered (ops ++ cons (i, j) nil) row col <->
    CellCovered ops row col \/
    ((row = i \/ row = i + 1) /\ (col = j \/ col = j + 1)).
Proof.
intros ops i j row col.
unfold CellCovered.
split.
- intros [x [y [Hin [Hr Hc]]]].
rewrite in_app_iff in Hin.
simpl in Hin.
destruct Hin as [Hin | [Heq | []]].
+ left.
exists x, y.
auto.
+ inversion Heq.
subst x y.
right.
auto.
- intros [[x [y [Hin [Hr Hc]]]] | [Hr Hc]].
+ exists x, y.
split; [rewrite in_app_iff; auto|auto].
+ exists i, j.
split; [rewrite in_app_iff; simpl; auto|auto].
Qed.

Lemma Znth_made_state__square_decision_transition :
  forall ops k,
    0 <= k < 2500 ->
    Znth k (made_state ops) 0 = made_cell ops (Z.to_nat k).
Proof.
intros ops k Hk.
unfold Znth, made_state.
assert (Hkn : (Z.to_nat k < 2500)%nat) by lia.
rewrite (@nth_indep Z
    (map (made_cell ops) (seq 0%nat 2500%nat))
    (Z.to_nat k) 0 (made_cell ops 0%nat))
    by (rewrite length_map, length_seq; exact Hkn).
rewrite map_nth.
rewrite seq_nth by exact Hkn.
rewrite Nat.add_0_l.
reflexivity.
Qed.

Lemma Zlength_replace_Znth__square_decision_transition :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
intros A l.
induction l; simpl in *; intros; auto.
unfold replace_Znth in *.
destruct (Z.to_nat n).
- simpl.
do 2 rewrite Zlength_cons.
lia.
- simpl.
do 2 rewrite Zlength_cons.
specialize (IHl (Z.of_nat n0) v).
replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
rewrite IHl.
lia.
Qed.

Lemma made_state_snoc__square_decision_transition :
  forall ops i j,
    0 <= i < 49 -> 0 <= j < 49 ->
    replace_Znth ((i + 1) * 50 + (j + 1)) 1
      (replace_Znth (i * 50 + (j + 1)) 1
        (replace_Znth ((i + 1) * 50 + j) 1
          (replace_Znth (i * 50 + j) 1 (made_state ops)))) =
    made_state (ops ++ cons (i, j) nil).
Proof.
intros ops i j Hi Hj.
apply (proj2 (list_eq_ext _ _ 0)).
assert (Hlen : Zlength (made_state ops) = 2500).
{ unfold made_state.
rewrite Zlength_correct, length_map, length_seq.
reflexivity.
}
  assert (Hlen' : Zlength (made_state (ops ++ cons (i, j) nil)) = 2500).
{ unfold made_state.
rewrite Zlength_correct, length_map, length_seq.
reflexivity.
}
  split.
- repeat rewrite Zlength_replace_Znth__square_decision_transition.
exact Hlen'.
- intros k Hk.
repeat rewrite Zlength_replace_Znth__square_decision_transition in Hk.
assert (Hidx1 : 0 <= i * 50 + j < 2500) by nia.
assert (Hidx2 : 0 <= (i + 1) * 50 + j < 2500) by nia.
assert (Hidx3 : 0 <= i * 50 + (j + 1) < 2500) by nia.
assert (Hidx4 : 0 <= (i + 1) * 50 + (j + 1) < 2500) by nia.
destruct (Z.eq_dec k ((i + 1) * 50 + (j + 1))) as [Ek4 | Ek4].
+ subst k.
rewrite Znth_replace_Znth_Same by
        (repeat rewrite Zlength_replace_Znth__square_decision_transition; exact Hidx4).
rewrite Znth_made_state__square_decision_transition by exact Hidx4.
unfold made_cell.
destruct (ClassicalEpsilon.excluded_middle_informative
        (CellCovered (ops ++ cons (i, j) nil)
          (Z.of_nat (Z.to_nat ((i + 1) * 50 + (j + 1))) / 50)
          (Z.of_nat (Z.to_nat ((i + 1) * 50 + (j + 1))) mod 50))) as [H | H];
        [reflexivity|].
exfalso.
apply H.
exists i, j.
split; [rewrite in_app_iff; simpl; auto|].
rewrite !Z2Nat.id by nia.
pose proof (flat_coord__square_decision_transition (i + 1) (j + 1) ltac:(lia)) as [Hd Hm].
auto.
+ destruct (Z.eq_dec k (i * 50 + (j + 1))) as [Ek3 | Ek3].
* subst k.
rewrite Znth_replace_Znth_Diff by
          (repeat rewrite Zlength_replace_Znth__square_decision_transition;
            try exact Hidx4; try exact Hidx3; nia).
rewrite Znth_replace_Znth_Same by
          (repeat rewrite Zlength_replace_Znth__square_decision_transition; exact Hidx3).
rewrite Znth_made_state__square_decision_transition by exact Hidx3.
unfold made_cell.
destruct (ClassicalEpsilon.excluded_middle_informative
          (CellCovered (ops ++ cons (i, j) nil)
            (Z.of_nat (Z.to_nat (i * 50 + (j + 1))) / 50)
            (Z.of_nat (Z.to_nat (i * 50 + (j + 1))) mod 50))) as [H | H];
          [reflexivity|].
exfalso.
apply H.
exists i, j.
split; [rewrite in_app_iff; simpl; auto|].
rewrite !Z2Nat.id by nia.
pose proof (flat_coord__square_decision_transition i (j + 1) ltac:(lia)) as [Hd Hm].
auto.
* destruct (Z.eq_dec k ((i + 1) * 50 + j)) as [Ek2 | Ek2].
-- subst k.
rewrite Znth_replace_Znth_Diff by
             (repeat rewrite Zlength_replace_Znth__square_decision_transition;
               try exact Hidx4; try exact Hidx2; nia).
rewrite Znth_replace_Znth_Diff by
             (repeat rewrite Zlength_replace_Znth__square_decision_transition;
               try exact Hidx3; try exact Hidx2; nia).
rewrite Znth_replace_Znth_Same by
             (repeat rewrite Zlength_replace_Znth__square_decision_transition; exact Hidx2).
rewrite Znth_made_state__square_decision_transition by exact Hidx2.
unfold made_cell.
destruct (ClassicalEpsilon.excluded_middle_informative
             (CellCovered (ops ++ cons (i, j) nil)
               (Z.of_nat (Z.to_nat ((i + 1) * 50 + j)) / 50)
               (Z.of_nat (Z.to_nat ((i + 1) * 50 + j)) mod 50))) as [H | H];
             [reflexivity|].
exfalso.
apply H.
exists i, j.
split; [rewrite in_app_iff; simpl; auto|].
rewrite !Z2Nat.id by nia.
pose proof (flat_coord__square_decision_transition (i + 1) j ltac:(lia)) as [Hd Hm].
auto.
-- destruct (Z.eq_dec k (i * 50 + j)) as [Ek1 | Ek1].
++ subst k.
rewrite Znth_replace_Znth_Diff by
                (repeat rewrite Zlength_replace_Znth__square_decision_transition;
                  try exact Hidx4; try exact Hidx1; nia).
rewrite Znth_replace_Znth_Diff by
                (repeat rewrite Zlength_replace_Znth__square_decision_transition;
                  try exact Hidx3; try exact Hidx1; nia).
rewrite Znth_replace_Znth_Diff by
                (repeat rewrite Zlength_replace_Znth__square_decision_transition;
                  try exact Hidx2; try exact Hidx1; nia).
rewrite Znth_replace_Znth_Same by
                (repeat rewrite Zlength_replace_Znth__square_decision_transition; exact Hidx1).
rewrite Znth_made_state__square_decision_transition by exact Hidx1.
unfold made_cell.
destruct (ClassicalEpsilon.excluded_middle_informative
                (CellCovered (ops ++ cons (i, j) nil)
                  (Z.of_nat (Z.to_nat (i * 50 + j)) / 50)
                  (Z.of_nat (Z.to_nat (i * 50 + j)) mod 50))) as [H | H];
                [reflexivity|].
exfalso.
apply H.
exists i, j.
split; [rewrite in_app_iff; simpl; auto|].
rewrite !Z2Nat.id by nia.
pose proof (flat_coord__square_decision_transition i j ltac:(lia)) as [Hd Hm].
auto.
++ repeat rewrite Znth_replace_Znth_Diff by
                (repeat rewrite Zlength_replace_Znth__square_decision_transition;
                  try assumption; nia).
rewrite !Znth_made_state__square_decision_transition by lia.
unfold made_cell.
assert (Hnatk : Z.of_nat (Z.to_nat k) = k) by
                (rewrite Z2Nat.id; lia).
assert (Hcov :
                CellCovered (ops ++ cons (i, j) nil) (k / 50) (k mod 50) <->
                CellCovered ops (k / 50) (k mod 50)).
{ rewrite CellCovered_snoc__square_decision_transition.
split; [|auto].
intros [Hold | [Hr Hc]]; [exact Hold|].
exfalso.
pose proof (Z.div_mod k 50 ltac:(lia)) as Hdm.
destruct Hr as [Hr | Hr]; destruct Hc as [Hc | Hc]; nia.
}
              rewrite Hnatk.
destruct (ClassicalEpsilon.excluded_middle_informative
                (CellCovered (ops ++ cons (i, j) nil) (k / 50) (k mod 50))) as [Hn | Hn];
              destruct (ClassicalEpsilon.excluded_middle_informative
                (CellCovered ops (k / 50) (k mod 50))) as [Ho | Ho];
                try reflexivity;
                [exfalso; apply Ho; apply Hcov; exact Hn
                |exfalso; apply Hn; apply Hcov; exact Ho].
Qed.

Lemma Zlength_replace_Znth__array_cell_extraction :
  forall {A : Type} (i : Z) (v : A) (xs : list A),
    Zlength (replace_Znth i v xs) = Zlength xs.
Proof.
intros A i v xs.
unfold replace_Znth.
repeat rewrite Zlength_correct.
assert (Hlength : forall k, length (replace_nth k xs v) = length xs).
{ intros k.
revert k.
induction xs as [|x xs IH]; intros [|k]; simpl; auto.
}
  rewrite Hlength.
reflexivity.
Qed.

Lemma CheckedPrefix_empty__validation_prefix_boundaries :
  forall n m a ops,
    CheckedPrefix n m a ops 0 0.
Proof.
unfold CheckedPrefix, BeforeCell.
intros n m a ops row col Hrow Hcol Hbefore.
destruct Hbefore as [Hrow_lt | [Hrow_eq Hcol_lt]]; lia.
Qed.

Lemma CheckedPrefix_row_advance__validation_prefix_boundaries :
  forall n m a ops i j,
    j = m ->
    CheckedPrefix n m a ops i j ->
    CheckedPrefix n m a ops (i + 1) 0.
Proof.
unfold CheckedPrefix, BeforeCell.
intros n m a ops i j Hj Hchecked row col Hrow Hcol Hbefore.
apply Hchecked; try assumption.
destruct Hbefore as [Hrow_lt | [Hrow_eq Hcol_lt]].
- destruct (Z.eq_dec row i) as [Hrow_eq | Hrow_neq].
+ right.
subst row j.
lia.
+ left.
lia.
- subst row j.
lia.
Qed.

Lemma made_state_index__validation_failure_result : forall ops row col,
  0 <= row < 50 -> 0 <= col < 50 ->
  (Znth (row * 50 + col) (made_state ops) 0 = 1 <->
   CellCovered ops row col) /\
  (~ CellCovered ops row col ->
   Znth (row * 50 + col) (made_state ops) 0 = 0).
Proof.
intros ops row col Hrow Hcol.
unfold made_state, Znth.
assert (Hidx : (Z.to_nat (row * 50 + col) <
                  length (map (made_cell ops) (seq 0 2500)))%nat).
{ rewrite length_map, length_seq.
apply (proj1 (Z2Nat.inj_lt (row * 50 + col) 2500
                   ltac:(lia) ltac:(lia))); lia.
}
  pose proof (@Coq.Lists.List.nth_indep Z
    (map (made_cell ops) (seq 0 2500))
    (Z.to_nat (row * 50 + col)) 0 (made_cell ops 0) Hidx) as Hindep.
rewrite Hindep.
rewrite Coq.Lists.List.map_nth.
rewrite Coq.Lists.List.seq_nth.
2: { apply (proj1 (Z2Nat.inj_lt (row * 50 + col) 2500
                       ltac:(lia) ltac:(lia))); lia.
}
  simpl.
unfold made_cell.
rewrite Z2Nat.id by lia.
rewrite Z.div_add_l by lia.
rewrite Z.div_small by lia.
rewrite Z.add_0_r.
replace (row * 50 + col) with (col + row * 50) by ring.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia.
destruct (ClassicalEpsilon.excluded_middle_informative
              (CellCovered ops row col))
    as [Hcovered | Hnot].
- split.
+ split; intro H; [exact Hcovered | reflexivity].
+ contradiction.
- split.
+ split; intro H; [discriminate | contradiction].
+ intros _.
reflexivity.
Qed.

Lemma CheckedPrefix_cell_advance__validation_failure_result :
  forall n m a ops i j,
    CheckedPrefix n m a ops i j ->
    0 <= i < n -> 0 <= j < m ->
    (Znth j (Znth i a nil) 0 = 1 <-> CellCovered ops i j) ->
    CheckedPrefix n m a ops i (j + 1).
Proof.
intros n m a ops i j Hprefix Hi Hj Hcurrent.
unfold CheckedPrefix in *.
intros row col Hrow Hcol Hbefore.
unfold BeforeCell in *.
destruct Hbefore as [Hrowlt | [Hroweq Hcollt]].
- apply Hprefix; [exact Hrow | exact Hcol |].
left.
exact Hrowlt.
- subst row.
destruct (Z_lt_le_dec col j) as [Hlt | Hle].
+ apply Hprefix; [exact Hi | exact Hcol |].
right.
auto.
+ assert (col = j) by lia.
subst col.
exact Hcurrent.
Qed.

Lemma scan_operations_unique_coverage__validation_failure_result :
  forall n m a scan ops,
    2 <= n -> 2 <= m ->
    ScanOperations n m a (n - 1) 0 scan ->
    FillingOperations n m a ops ->
    forall row col, 0 <= row < n -> 0 <= col < m ->
      (CellCovered scan row col <-> CellCovered ops row col).
Proof.
intros n m a scan ops Hn Hm Hscan Hfill row col Hrow Hcol.
destruct Hscan as [_ [Hscan_bounds Hscan_cells]].
destruct Hfill as [_ [Hops_bounds Hfill_cells]].
split.
- intros [x [y [Hin [Hrowxy Hcolxy]]]].
assert (Hxybounds : 0 <= x < n - 1 /\ 0 <= y < m - 1).
{ eapply Forall_forall in Hscan_bounds; [|exact Hin].
simpl in Hscan_bounds.
exact Hscan_bounds.
}
    destruct Hxybounds as [Hx Hy].
assert (Hall : SquareAllOn a x y).
{ apply (proj1 (Hscan_cells x y Hx Hy)) in Hin.
exact (proj2 Hin).
}
    apply (proj1 (Hfill_cells row col Hrow Hcol)).
unfold SquareAllOn in Hall.
destruct Hall as [H00 [H10 [H01 H11]]].
destruct Hrowxy as [-> | ->]; destruct Hcolxy as [-> | ->]; assumption.
- intros [x [y [Hin [Hrowxy Hcolxy]]]].
assert (Hxybounds : 0 <= x < n - 1 /\ 0 <= y < m - 1).
{ eapply Forall_forall in Hops_bounds; [|exact Hin].
simpl in Hops_bounds.
exact Hops_bounds.
}
    destruct Hxybounds as [Hx Hy].
assert (Hin_scan : In (x, y) scan).
{ apply (proj2 (Hscan_cells x y Hx Hy)).
split.
- unfold BeforeSquare.
left.
exact (proj2 Hx).
- unfold SquareAllOn.
assert (H00 : CellCovered ops x y).
{ exists x, y.
repeat split; auto.
}
        assert (H10 : CellCovered ops (x + 1) y).
{ exists x, y.
repeat split; auto.
}
        assert (H01 : CellCovered ops x (y + 1)).
{ exists x, y.
repeat split; auto.
}
        assert (H11 : CellCovered ops (x + 1) (y + 1)).
{ exists x, y.
repeat split; auto.
}
        repeat split.
+ apply (proj2 (Hfill_cells x y ltac:(lia) ltac:(lia))).
exact H00.
+ apply (proj2 (Hfill_cells (x + 1) y ltac:(lia) ltac:(lia))).
exact H10.
+ apply (proj2 (Hfill_cells x (y + 1) ltac:(lia) ltac:(lia))).
exact H01.
+ apply (proj2 (Hfill_cells (x + 1) (y + 1)
                         ltac:(lia) ltac:(lia))).
exact H11.
}
    unfold CellCovered.
exists x, y.
repeat split; assumption.
Qed.

Lemma mismatch_implies_no_filling__validation_failure_result :
  forall n m a scan row col,
    2 <= n <= 50 -> 2 <= m <= 50 ->
    0 <= row < n -> 0 <= col < m ->
    (Znth col (Znth row a nil) 0 = 0 \/
     Znth col (Znth row a nil) 0 = 1) ->
    ScanOperations n m a (n - 1) 0 scan ->
    Znth col (Znth row a nil) 0 <>
      Znth (row * 50 + col) (made_state scan) 0 ->
    forall ops, ~ FillingOperations n m a ops.
Proof.
intros n m a scan row col Hn Hm Hrow Hcol Hbinary Hscan Hmismatch.
intros ops Hfill.
pose proof (scan_operations_unique_coverage__validation_failure_result
    n m a scan ops (proj1 Hn) (proj1 Hm) Hscan Hfill row col Hrow Hcol)
    as Hcoverage.
pose proof (proj2 (proj2 Hfill)) as Hfill_cells.
pose proof (made_state_index__validation_failure_result scan row col
    ltac:(lia) ltac:(lia)) as [Hmade_one Hmade_zero].
destruct Hbinary as [Hzero | Hone].
- assert (Hnot_ops : ~ CellCovered ops row col).
{ intro Hcovered.
pose proof (proj2 (Hfill_cells row col Hrow Hcol) Hcovered).
lia.
}
    assert (Hnot_scan : ~ CellCovered scan row col).
{ intro Hcovered.
apply Hnot_ops.
apply (proj1 Hcoverage).
exact Hcovered.
}
    specialize (Hmade_zero Hnot_scan).
apply Hmismatch.
lia.
- assert (Hops : CellCovered ops row col).
{ apply (proj1 (Hfill_cells row col Hrow Hcol)).
exact Hone.
}
    assert (Hscan_cover : CellCovered scan row col).
{ apply (proj2 Hcoverage).
exact Hops.
}
    pose proof (proj2 Hmade_one Hscan_cover) as Hmade.
apply Hmismatch.
lia.
Qed.

Lemma completed_scan_filling__successful_result :
  forall n m a ops,
    Zlength ops <= 2500 ->
    ScanOperations n m a (n - 1) 0 ops ->
    CheckedPrefix n m a ops n 0 ->
    FillingOperations n m a ops.
Proof.
intros n m a ops Hcap Hscan Hchecked.
destruct Hscan as [_ [Hbounds _]].
unfold FillingOperations.
split; [exact Hcap |].
split; [exact Hbounds |].
intros i j Hi Hj.
apply Hchecked; try assumption.
unfold BeforeCell.
left; lia.
Qed.

Lemma operation_words_Zlength__successful_result :
  forall ops,
    Zlength (operation_words ops) = 2 * Zlength ops.
Proof.
unfold operation_words.
induction ops as [| [x y] ops IH]; simpl.
- reflexivity.
- rewrite !Zlength_cons, IH.
change (Z.succ (Z.succ (2 * Zlength ops)) =
      2 * Z.succ (Zlength ops)).
rewrite Z.mul_succ_r.
lia.
Qed.

Lemma operation_words_pair__successful_result :
  forall ops k (option_default : option Z) (pair_default : Z * Z),
    0 <= k < Zlength ops ->
    Znth (2 * k) (operation_words ops) option_default =
      Some (fst (Znth k ops pair_default) + 1) /\
    Znth (2 * k + 1) (operation_words ops) option_default =
      Some (snd (Znth k ops pair_default) + 1).
Proof.
unfold operation_words.
induction ops as [| [x y] ops IH]; intros k option_default pair_default Hk.
- rewrite Zlength_nil in Hk.
lia.
- rewrite Zlength_cons in Hk.
destruct (Z.eq_dec k 0) as [-> | Hk0].
+ unfold Znth.
cbn.
auto.
+ assert (0 < k) by lia.
change
        (Znth (2 * k)
           (Some (x + 1) :: Some (y + 1) ::
             flat_map
               (fun p : Z * Z =>
                  cons (Some (fst p + 1))
                    (cons (Some (snd p + 1)) nil)) ops)
           option_default =
           Some (fst (Znth k ((x, y) :: ops) pair_default) + 1) /\
         Znth (2 * k + 1)
           (Some (x + 1) :: Some (y + 1) ::
             flat_map
               (fun p : Z * Z =>
                  cons (Some (fst p + 1))
                    (cons (Some (snd p + 1)) nil)) ops)
           option_default =
           Some (snd (Znth k ((x, y) :: ops) pair_default) + 1)).
repeat rewrite Znth_cons by lia.
replace (2 * k - 1 - 1) with (2 * (k - 1)) by lia.
replace (2 * k + 1 - 1 - 1) with (2 * (k - 1) + 1) by lia.
apply IH.
lia.
Qed.

Lemma staged_ops_pair_index__successful_result :
  forall ops k (option_default : option Z) (pair_default : Z * Z),
    Zlength ops <= 2500 ->
    0 <= k < Zlength ops ->
    Znth (2 * k) (staged_ops ops) option_default =
      Some (fst (Znth k ops pair_default) + 1) /\
    Znth (2 * k + 1) (staged_ops ops) option_default =
      Some (snd (Znth k ops pair_default) + 1).
Proof.
intros ops k option_default pair_default Hcap Hk.
unfold staged_ops.
rewrite !app_Znth1.
- apply operation_words_pair__successful_result.
exact Hk.
- rewrite operation_words_Zlength__successful_result.
lia.
- rewrite operation_words_Zlength__successful_result.
lia.
Qed.
