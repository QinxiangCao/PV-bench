(* Codeforces 509/E - Pretty Song: sum, over all substrings, the fraction of
   vowels in the substring. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope R_scope.

(* c is a vowel: I, E, A, O, U or Y, codes 73, 69, 65, 79, 85, 89. *)
Definition Vowel (c : Z) : Prop := c = 73%Z \/ c = 69%Z \/ c = 65%Z \/ c = 79%Z \/ c = 85%Z \/ c = 89%Z.
Definition Pre (s : list Z) : Prop :=
  (* Stated explicitly in the P070 solver Require, so dropped here:
       (1 <= Zlength s <= 500000)%Z /\
       Forall (fun c => (65 <= c <= 90)%Z) s  *)
  True.

(* out = sum over 0 <= i <= j < |s| of
           #{ q : i <= q <= j and s[q] is a vowel } / (j - i + 1)
   i.e. the simple prettiness of every substring, added up as a real number. *)
Definition Spec (s : list Z) (out : R) : Prop :=
  out = sum_range_R 0%Z (Zlength s - 1)%Z (fun i =>
    sum_range_R i (Zlength s - 1)%Z (fun j =>
      IZR (#(fun q : Z => (i <= q < j + 1)%Z /\ Vowel (Znth q s 0%Z))) / IZR ((j - i + 1)%Z))).

(* Representation helper for the solver contract: vowels counted over all windows
   of one fixed length, sum over i of #{ vowels in s[i..i+len) }. *)
Definition PrettyTerm (s : list Z) (len : Z) : Z :=
  sum_range 0 (Zlength s - len) (fun i =>
    #(fun q : Z => (i <= q < i + len)%Z /\ Vowel (Znth q s 0%Z))).

(* The table of those totals, one per length. *)
Definition PrettyTermTable (s terms : list Z) : Prop :=
  Zlength terms = Zlength s /\
  forall len, (1 <= len <= Zlength s)%Z ->
    Znth (len - 1)%Z terms 0%Z = PrettyTerm s len.

(* The same total regrouped by substring length:
     out = sum over len in 1..|s| of PrettyTerm(s, len) / len
   since every substring of length len contributes with the same denominator. *)
Definition PrettyTerms (s terms : list Z) (out : R) : Prop :=
  PrettyTermTable s terms /\
  out = sum_range_R 1 (Zlength s) (fun len =>
          Rdiv (IZR (Znth (len - 1)%Z terms 0%Z)) (IZR len)).
