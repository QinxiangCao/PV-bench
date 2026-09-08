Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The pointwise least strictly increasing profile above an input prefix. *)
Definition LeftProfilePrefix (a p : list Z) : Prop :=
  1 <= Zlength p <= Zlength a /\
  (forall i, 0 <= i < Zlength p -> Znth i a 0 <= Znth i p 0) /\
  (forall i, 0 <= i < Zlength p - 1 ->
     Znth i p 0 < Znth (i + 1) p 0) /\
  forall q,
    Zlength q = Zlength p ->
    (forall i, 0 <= i < Zlength q -> Znth i a 0 <= Znth i q 0) ->
    (forall i, 0 <= i < Zlength q - 1 ->
       Znth i q 0 < Znth (i + 1) q 0) ->
    forall i, 0 <= i < Zlength p -> Znth i p 0 <= Znth i q 0.

(* The pointwise least strictly decreasing profile above an input suffix.
   [p] corresponds to [sublist (Zlength a - Zlength p) (Zlength a) a]. *)
Definition RightProfileSuffix (a p : list Z) : Prop :=
  1 <= Zlength p <= Zlength a /\
  (forall j, 0 <= j < Zlength p ->
     Znth (Zlength a - Zlength p + j) a 0 <= Znth j p 0) /\
  (forall j, 0 <= j < Zlength p - 1 ->
     Znth j p 0 > Znth (j + 1) p 0) /\
  forall q,
    Zlength q = Zlength p ->
    (forall j, 0 <= j < Zlength q ->
       Znth (Zlength a - Zlength q + j) a 0 <= Znth j q 0) ->
    (forall j, 0 <= j < Zlength q - 1 ->
       Znth j q 0 > Znth (j + 1) q 0) ->
    forall j, 0 <= j < Zlength p -> Znth j p 0 <= Znth j q 0.

(* Cumulative added load for a completed left profile prefix. *)
Definition PrefixCosts (a inc pre : list Z) : Prop :=
  Zlength pre = Zlength inc /\ Zlength inc <= Zlength a /\
  forall i, 0 <= i < Zlength pre ->
    Znth i pre 0 =
      sum_range 0 i (fun k => Znth k inc 0 - Znth k a 0).

(* Cumulative added load for a completed right profile suffix.  Both lists
   use suffix-relative indexing. *)
Definition SuffixCosts (a dec suf : list Z) : Prop :=
  Zlength suf = Zlength dec /\ Zlength dec <= Zlength a /\
  forall j, 0 <= j < Zlength suf ->
    Znth j suf 0 =
      sum_range j (Zlength suf - 1)
        (fun k =>
           Znth k dec 0 -
           Znth (Zlength a - Zlength suf + k) a 0).

Definition PeakCostValue
    (a inc dec pre suf : list Z) (i : Z) : Z :=
  Znth i pre 0 + Znth i suf 0 - (Znth i inc 0 - Znth i a 0) -
  (Znth i dec 0 - Znth i a 0) +
  (Z.max (Znth i inc 0) (Znth i dec 0) - Znth i a 0).

(* [best] is the least candidate cost among peaks in [0, upto).  The sentinel
   -1 is used only for the empty prefix, exactly as in the C code. *)
Definition BestPeakPrefix
    (a inc dec pre suf : list Z) (upto best : Z) : Prop :=
  (upto = 0 /\ best = -1) \/
  (0 < upto /\ upto <= Zlength a /\
   exists peak,
     0 <= peak < upto /\
     best = PeakCostValue a inc dec pre suf peak /\
     forall j, 0 <= j < upto ->
       best <= PeakCostValue a inc dec pre suf j).

(* Cumulative costs for the portion of [pre] written so far.  The increasing
   profile may already be complete, so its length need only bound [pre]. *)
Definition PartialPrefixCosts (a inc pre : list Z) : Prop :=
  Zlength pre <= Zlength inc /\ Zlength inc <= Zlength a /\
  forall i, 0 <= i < Zlength pre ->
    Znth i pre 0 =
      sum_range 0 i (fun k => Znth k inc 0 - Znth k a 0).

(* Cumulative costs for the written suffix of a complete decreasing profile.
   Both [dec] and [a] are addressed using the suffix offset determined by the
   current length of [suf]. *)
Definition PartialSuffixCosts (a dec suf : list Z) : Prop :=
  Zlength suf <= Zlength dec /\ Zlength dec <= Zlength a /\
  forall j, 0 <= j < Zlength suf ->
    Znth j suf 0 =
      sum_range j (Zlength suf - 1)
        (fun k =>
           Znth (Zlength dec - Zlength suf + k) dec 0 -
           Znth (Zlength a - Zlength suf + k) a 0).
