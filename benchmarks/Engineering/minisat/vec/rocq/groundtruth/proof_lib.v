Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From compcert.lib Require Import Integers.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Import naive_C_Rules.
Local Open Scope sac.

(**
  Allocation arithmetic used by a live vector.  The array predicates carry
  the concrete allocation span; this pure interface records the corresponding
  UInt32 byte-count side condition used by the current C front end.
 *)
Require Export PVbench.Engineering.minisat.vec.rocq.spec_lib.
Require Import Coq.micromega.Lia.

Lemma veci_buffer_truncate__resize_prefix :
  forall (buf : addr) (xs : list Z) (cap k : Z),
    0 <= k <= Zlength xs ->
    Zlength xs <= cap ->
    IntArray.full buf (Zlength xs) xs **
    IntArray.undef_seg buf (Zlength xs) cap |--
    IntArray.full buf k (sublist 0 k xs) **
    IntArray.undef_seg buf k cap.
Proof.
  intros.
  sep_apply (IntArray.full_split_to_seg buf k (Zlength xs) xs); try lia.
  sep_apply (IntArray.seg_to_full buf 0 k (sublist 0 k xs)).
  replace (buf + 0 * sizeof(INT)) with buf by lia.
  replace (k - 0) with k by lia.
  sep_apply (IntArray.seg_to_undef_seg
    buf k (Zlength xs) (sublist k (Zlength xs) xs)).
  sep_apply (IntArray.undef_seg_merge_to_undef_seg
    buf k (Zlength xs) cap); try lia.
  cancel (IntArray.full buf k (sublist 0 k xs)).
  cancel (IntArray.undef_seg buf k cap).
Qed.

Lemma vecp_buffer_truncate__resize_prefix :
  forall (buf : addr) (xs : list Z) (cap k : Z),
    0 <= k <= Zlength xs ->
    Zlength xs <= cap ->
    PtrArray.full buf (Zlength xs) xs **
    PtrArray.undef_seg buf (Zlength xs) cap |--
    PtrArray.full buf k (sublist 0 k xs) **
    PtrArray.undef_seg buf k cap.
Proof.
  intros.
  sep_apply (PtrArray.full_split_to_seg buf k (Zlength xs) xs); try lia.
  sep_apply (PtrArray.seg_to_full buf 0 k (sublist 0 k xs)).
  replace (buf + 0 * ptr_size_Z) with buf by lia.
  replace (k - 0) with k by lia.
  sep_apply (PtrArray.seg_to_undef_seg
    buf k (Zlength xs) (sublist k (Zlength xs) xs)).
  sep_apply (PtrArray.undef_seg_merge_to_undef_seg
    buf k (Zlength xs) cap); try lia.
  cancel (PtrArray.full buf k (sublist 0 k xs)).
  cancel (PtrArray.undef_seg buf k cap).
Qed.

Lemma reassociate_sepcon_7_entail__push_nongrowth
    {P1 P2 P3 P4 P5 P6 P7 Q : Assertion} :
  (P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 |-- Q) ->
  (P1 ** (P2 ** (P3 ** (P4 ** (P5 ** (P6 ** P7)))))) |-- Q.
Proof.
  intros H.
  sep_apply H.
  cancel.
Qed.

Lemma vec_push_result_from_branches__push_final :
  forall len oldbuf oldcap newbuf newcap,
    len <= oldcap ->
    len < newcap ->
    (len < oldcap -> newbuf = oldbuf /\ newcap = oldcap) ->
    (len = oldcap -> newcap = 2 * oldcap + 1) ->
    vec_push_result len oldbuf oldcap newbuf newcap.
Proof.
  intros len oldbuf oldcap newbuf newcap Hle Hnew Hsame Hgrow.
  unfold vec_push_result.
  destruct (Z_lt_ge_dec len oldcap) as [Hlt | Hge].
  - left. split; [exact Hlt | exact (Hsame Hlt)].
  - right. assert (Heq : len = oldcap) by lia.
    split; [exact Heq | exact (Hgrow Heq)].
Qed.
