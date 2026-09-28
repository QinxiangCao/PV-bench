Require Export PVbench.Codeforces.examples_shard00.P089_1891E_brukhovich_and_exams.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Require Import Coq.Sorting.Permutation.

Import ListNotations.

Definition GcdResult (x y result : Z) : Prop :=
  result = Z.gcd x y.

Definition MinValue (x y result : Z) : Prop :=
  result = Z.min x y.

Definition AllOnePrefix (a : list Z) (hi flag : Z) : Prop :=
  (flag = 1 /\ forall j, 0 <= j < hi -> Znth j a 0 = 1) \/
  (flag = 0 /\ exists j, 0 <= j < hi /\ Znth j a 0 <> 1).

Definition AdjacentCoprime (a : list Z) (i : Z) : Prop :=
  0 <= i < Zlength a - 1 /\
  Z.gcd (Znth i a 0) (Znth (i + 1) a 0) = 1.

Definition CoprimeEdgePrefixCount
    (a : list Z) (hi count : Z) : Prop :=
  count = #(fun i : Z => 0 <= i < hi /\ AdjacentCoprime a i).

Definition NonOnePairCenter (a : list Z) (hi center : Z) : Prop :=
  1 <= center < hi - 1 /\
  Znth (center - 1) a 0 <> 1 /\
  Znth center a 0 <> 1 /\
  Znth (center + 1) a 0 <> 1 /\
  AdjacentCoprime a (center - 1) /\
  AdjacentCoprime a center.

Definition PairCenterSelection
    (a : list Z) (hi : Z) (chosen : Z -> Prop) : Prop :=
  (forall center, chosen center -> NonOnePairCenter a hi center) /\
  (forall x y, chosen x -> chosen y -> x <> y -> 2 <= Z.abs (x - y)).

Definition PairSavingsPrefix (a : list Z) (hi savings : Z) : Prop :=
  max_value_of_subset Z.le
    (fun chosen : Z -> Prop => PairCenterSelection a hi chosen)
    (fun chosen => #(fun center : Z =>
       1 <= center < hi - 1 /\ chosen center)) savings.

Definition PairSavingsScan
    (a : list Z) (hi committed pending savings : Z) : Prop :=
  savings = committed + pending / 2 /\
  0 <= pending < hi /\
  PairSavingsPrefix a hi savings.

Definition PairRunSuffix (a : list Z) (hi pending : Z) : Prop :=
  let start := hi - pending - 1 in
  0 <= start < hi /\
  (forall j, start <= j < hi -> Znth j a 0 <> 1) /\
  (forall j, start <= j < hi - 1 -> AdjacentCoprime a j) /\
  (start = 0 \/ Znth (start - 1) a 0 = 1 \/
    ~ AdjacentCoprime a (start - 1)).

Definition InteriorOneBlock (a : list Z) (lo hi : Z) : Prop :=
  0 < lo < hi /\ hi < Zlength a /\
  Znth (lo - 1) a 0 <> 1 /\ Znth hi a 0 <> 1 /\
  forall j, lo <= j < hi -> Znth j a 0 = 1.

Definition InteriorOneRunPrefix
    (a : list Z) (limit : Z) (lengths : list Z) : Prop :=
  exists starts,
    Zlength starts = Zlength lengths /\
    ListLib.increasing starts /\
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0) /\
      Znth q starts 0 + Znth q lengths 0 <= limit) /\
    (forall lo hi, InteriorOneBlock a lo hi -> hi <= limit ->
      exists q, 0 <= q < Zlength lengths /\
        Znth q starts 0 = lo /\ Znth q lengths 0 = hi - lo).

Definition OneRunScanState
    (a : list Z) (lo next : Z) (lengths : list Z) : Prop :=
  InteriorOneRunPrefix a lo lengths /\
  (forall j, lo <= j < next -> Znth j a 0 = 1).

Definition GreedyBlockState
    (sorted : list Z) (next budget initial_sad remaining sadness : Z) : Prop :=
  0 <= next <= Zlength sorted /\
  remaining = budget - ListLib.sum (sublist 0 next sorted) /\
  sadness = initial_sad -
    ListLib.sum (map (fun len => len + 1) (sublist 0 next sorted)) /\
  (forall j, 0 <= j < next ->
    Znth j sorted 0 <=
      budget - ListLib.sum (sublist 0 j sorted)).

Definition FinalBudgetResult
    (remaining sadness out : Z) : Prop :=
  out = Z.max 0 (sadness - Z.min remaining sadness).

Definition ExamOptimizationSummary
    (a : list Z) (base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  ExamSadness a base_sad /\
  PairSavingsPrefix a (Zlength a) pair_savings /\
  InteriorOneRunPrefix a (Zlength a) block_lengths /\
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    Spec original_k a out.

Definition OptimizationSafetyBounds
    (base_sad pair_savings : Z) (block_lengths : list Z) : Prop :=
  0 <= pair_savings /\
  Forall (fun len => 1 <= len) block_lengths /\
  2 * pair_savings +
    ListLib.sum (map (fun len => len + 1) block_lengths) <= base_sad.

(** A concrete joint witness for the savings already discovered by the two
    structural scans.  Unlike the two independent summary predicates above,
    this predicate fixes one maximum set of pair centres and one ordered list
    of one-block starts at the same time, and records that their covered edge
    intervals are disjoint.  The numeric prefix bound is therefore a genuine
    charging invariant, not merely a later arithmetic assertion. *)
Definition JointPairBlockPrefix
    (a : list Z) (limit base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  PairSavingsPrefix a (Zlength a) pair_savings /\
  InteriorOneRunPrefix a limit block_lengths /\
  0 <= pair_savings /\
  Forall (fun len => 1 <= len) block_lengths /\
  2 * pair_savings +
    ListLib.sum (map (fun len => len + 1) block_lengths) <= base_sad /\
  exists (centres : Z -> Prop) (starts : list Z),
    PairCenterSelection a (Zlength a) centres /\
    #(fun center : Z =>
        1 <= center < Zlength a - 1 /\ centres center) = pair_savings /\
    Zlength starts = Zlength block_lengths /\
    ListLib.increasing starts /\
    (forall q, 0 <= q < Zlength block_lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q block_lengths 0) /\
      Znth q starts 0 + Znth q block_lengths 0 <= limit) /\
    (forall center q,
      centres center -> 0 <= q < Zlength block_lengths ->
      center < Znth q starts 0 - 1 \/
      Znth q starts 0 + Znth q block_lengths 0 < center).

Definition ExamOptimalityEvidence
    (a : list Z) (original_k out : Z) : Prop :=
  exists result,
    SimplifiedExams a original_k result /\
    ExamSadness result out /\
    forall other other_sadness,
      SimplifiedExams a original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.

(** The exchange certificate deliberately exposes both halves of optimality:
    construction of an attainable stopped-greedy value and the charging lower
    bound against every admissible simplification. *)
Definition ExamJointOptimizationCertificate
    (a : list Z) (base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  JointPairBlockPrefix a (Zlength a) base_sad pair_savings block_lengths /\
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    ExamOptimalityEvidence a original_k out.

Require Import Coq.micromega.Lia.

(** A competitor is restricted at a scan prefix when it does not completely
    erase an interior one-block whose right boundary has not yet been reached.
    This is the stable semantic distinction made by the second structural
    scan: completed blocks are available for the extra one-edge saving, while
    every later block must still leave at least one of its one entries
    unchosen. *)
Definition RestrictedSimplifiedExams
    (a : list Z) (limit k : Z) (result : list Z) : Prop :=
  exists chosen : Z -> Prop,
    (forall i, chosen i -> 0 <= i < Zlength a) /\
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
    Zlength result = Zlength a /\
    (forall i, 0 <= i < Zlength a ->
      Znth i result 0 = if prop_dec (chosen i) then 0 else Znth i a 0) /\
    forall lo hi,
      InteriorOneBlock a lo hi -> limit < hi ->
      exists j, lo <= j < hi /\ ~ chosen j.

Definition ExamRestrictedOptimalityEvidence
    (a : list Z) (limit original_k out : Z) : Prop :=
  exists result,
    SimplifiedExams a original_k result /\
    ExamSadness result out /\
    forall other other_sadness,
      RestrictedSimplifiedExams a limit original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.

(** Universal exchange/charging state owned by the one-block scan.  The
    restriction weakens monotonically as [limit] advances and disappears at
    the full-array limit. *)
Definition ExamCompetitorChargingPrefix
    (a : list Z) (limit base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    ExamRestrictedOptimalityEvidence a limit original_k out.

(** A future-aware certificate for the one-block collection phase.  Rather
    than assigning the final greedy answer to the blocks already discovered
    at a cursor (which is unsound in the presence of zero endpoints), it
    quantifies over every suffix completing the current prefix to the exact
    full interior-block profile. *)
Definition ExamBlockCollectionCertificate
    (a : list Z) (base_sad pair_savings : Z)
    (collected : list Z) : Prop :=
  forall future,
    InteriorOneRunPrefix a (Zlength a) (collected ++ future) ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings (collected ++ future).

(** A simplification restricted to indices strictly before [limit].  This is
    the competitor family that the one-block scan can soundly grow: the inner
    one-run loop keeps the limit at the run start, and the outer loop advances
    it only after the complete run (and its all-or-nothing bonus) is known. *)
Definition PrefixSimplifiedExams
    (a : list Z) (limit k : Z) (result : list Z) : Prop :=
  exists chosen : Z -> Prop,
    (forall i, chosen i -> 0 <= i < Zlength a) /\
    (forall i, chosen i -> i < limit) /\
    #(fun i : Z => 0 <= i < Zlength a /\ chosen i) <= k /\
    Zlength result = Zlength a /\
    forall i, 0 <= i < Zlength a ->
      Znth i result 0 =
        if prop_dec (chosen i) then 0 else Znth i a 0.

(** The scan owns only the universal lower-bound half of optimality.  Unlike
    [ExamCompetitorChargingPrefix], this state does not claim that the
    temporary value for an incomplete block profile is already attainable. *)
Definition ExamPrefixLowerBound
    (a : list Z) (limit base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  limit = 0 \/
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    forall other other_sadness,
      PrefixSimplifiedExams a limit original_k other ->
      ExamSadness other other_sadness ->
      out <= other_sadness.

(** The constructive half is deliberately requested only after the exact full
    block profile has been collected. *)
Definition ExamGreedyAttainability
    (a : list Z) (base_sad pair_savings : Z)
    (block_lengths : list Z) : Prop :=
  forall original_k sorted use next remaining sadness out,
    1 <= original_k <= Zlength a ->
    Permutation block_lengths sorted ->
    ListLib.increasing sorted ->
    MinValue original_k pair_savings use ->
    GreedyBlockState sorted next (original_k - use)
      (base_sad - 2 * use) remaining sadness ->
    (next = Zlength sorted \/ Znth next sorted 0 > remaining) ->
    FinalBudgetResult remaining sadness out ->
    exists result,
      SimplifiedExams a original_k result /\ ExamSadness result out.

(** Canonical form of the interior-one-block profile.  The legacy
    [InteriorOneRunPrefix] deliberately used nondecreasing starts; the strict
    order here records each maximal block at most once and therefore rules out
    duplicate occurrences of the same block. *)
Definition CanonicalInteriorOneRunPrefix
    (a : list Z) (limit : Z) (lengths : list Z) : Prop :=
  exists starts,
    Zlength starts = Zlength lengths /\
    mono_inc starts /\
    (forall q, 0 <= q < Zlength lengths ->
      InteriorOneBlock a (Znth q starts 0)
        (Znth q starts 0 + Znth q lengths 0) /\
      Znth q starts 0 + Znth q lengths 0 <= limit) /\
    (forall lo hi, InteriorOneBlock a lo hi -> hi <= limit ->
      exists q, 0 <= q < Zlength lengths /\
        Znth q starts 0 = lo /\ Znth q lengths 0 = hi - lo).

Definition CanonicalOneRunScanState
    (a : list Z) (lo next : Z) (lengths : list Z) : Prop :=
  CanonicalInteriorOneRunPrefix a lo lengths /\
  (forall j, lo <= j < next -> Znth j a 0 = 1).

(** The future certificate ranges only over canonical full profiles.  This is
    exactly the family produced by the left-to-right maximal-run scan. *)
Definition CanonicalExamBlockCollectionCertificate
    (a : list Z) (base_sad pair_savings : Z)
    (collected : list Z) : Prop :=
  forall future,
    CanonicalInteriorOneRunPrefix
      a (Zlength a) (collected ++ future) ->
    ExamJointOptimizationCertificate
      a base_sad pair_savings (collected ++ future).

Require Import Coq.ZArith.Zquot.
