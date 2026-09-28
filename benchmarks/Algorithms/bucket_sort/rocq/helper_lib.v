Require Export PVbench.Algorithms.bucket_sort.rocq.spec_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Sorting.Permutation.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From Coq Require Import Lia.
Require Import Coq.ZArith.Zquot.
(** Group-local mathematical support for the reverse stable-placement loop. *)
Require Import Coq.Sorting.Sorted Coq.micromega.Lia Coq.micromega.Psatz.
From Coq Require Import Lia Zquot.

(** The decimal digit selected by one LSD pass.  [exponent] is kept as an
    explicit argument because the C annotation separately owns its positivity
    and machine range. *)
Definition RadixDigit (value exponent : Z) : Z :=
  (value / exponent) mod 10.

(** Maximum of the mathematical prefix [0,hi), using the shared extremum
    semantics. Valid prefix indices are the candidate set; access safety is
    supplied separately by the C contract. *)
Definition PrefixMaximum (values : list Z) (hi maximum : Z) : Prop :=
  max_value_of_subset Z.le (fun index : Z => 0 <= index < hi)
    (fun index => Znth index values 0) maximum.

(** Decimal powers, independent of the implementation's machine bounds. *)
Definition DecimalExponent (exponent : Z) : Prop :=
  exists power : Z, 0 <= power /\ exponent = 10 ^ power.

(** Ordering by all decimal positions already processed before [exponent]. *)
Definition RadixLowerDigitsOrdered
    (values : list Z) (exponent : Z) : Prop :=
  forall left right,
    0 <= left /\ left <= right /\ right < Zlength values ->
    (Znth left values 0) mod exponent <=
    (Znth right values 0) mod exponent.

(** Stable public-facing mathematical state at the head of an LSD pass. *)
Definition RadixPassState
    (input current : list Z) (exponent : Z) : Prop :=
  Permutation input current /\
  RadixLowerDigitsOrdered current exponent.

Definition RadixBucket
    (values : list Z) (exponent digit : Z) : list Z :=
  filter
    (fun value => Z.eqb (RadixDigit value exponent) digit)
    values.

Definition RadixDigitCount
    (values : list Z) (exponent hi digit : Z) : Z :=
  Zlength (RadixBucket (sublist 0 hi values) exponent digit).

(** Exact ten-way histogram for the processed source prefix. *)
Definition DigitHistogramPrefix
    (values : list Z) (exponent hi : Z) (counts : list Z) : Prop :=
  forall digit,
    0 <= digit < 10 ->
    Znth digit counts 0 = RadixDigitCount values exponent hi digit.

(** During the prefix-sum loop, buckets below [processed] are cumulative
    exclusive endpoints; the rest still contain raw histogram counts. *)
Definition DigitPrefixTotals
    (histogram totals : list Z) (processed : Z) : Prop :=
  forall digit,
    0 <= digit < 10 ->
    (digit < processed ->
       Znth digit totals 0 = sum (sublist 0 (digit + 1) histogram)) /\
    (processed <= digit ->
       Znth digit totals 0 = Znth digit histogram 0).

Definition RadixBucketStart (histogram : list Z) (digit : Z) : Z :=
  sum (sublist 0 digit histogram).

Definition RadixBucketEnd (histogram : list Z) (digit : Z) : Z :=
  sum (sublist 0 (digit + 1) histogram).

(** Canonical stable decimal-bucket result: concatenate, in digit order, the
    source subsequences selected by each digit.  This is a mathematical stable
    partition, not an interpreter for the C loops. *)
Definition RadixStableOutput
    (source : list Z) (exponent : Z) : list Z :=
  concat
    (map
       (fun digit => RadixBucket source exponent digit)
       [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]).

Definition StableDigitPass
    (source output : list Z) (exponent : Z) : Prop :=
  output = RadixStableOutput source exponent.

(** [remaining] is the unprocessed source-prefix length during the reverse
    stable-placement loop.  Counters delimit the still-empty bucket prefixes;
    the corresponding suffixes in [mixed_output] already reveal the canonical
    stable result as [Some], and every other local-output cell is [None]. *)
Definition BucketPlacementProgress
    (source : list Z) (exponent remaining : Z)
    (histogram counters : list Z)
    (mixed_output : list (option Z)) : Prop :=
  (forall digit,
      0 <= digit < 10 ->
      Znth digit counters 0 =
        RadixBucketStart histogram digit +
        RadixDigitCount source exponent remaining digit) /\
  (forall digit,
      0 <= digit < 10 ->
      RadixBucketStart histogram digit <= Znth digit counters 0 <=
      RadixBucketEnd histogram digit) /\
  (forall digit position,
      0 <= digit < 10 ->
      Znth digit counters 0 <= position <
        RadixBucketEnd histogram digit ->
      Znth position mixed_output None =
        Some (Znth position (RadixStableOutput source exponent) 0)) /\
  (forall position,
      0 <= position < Zlength mixed_output ->
      (forall digit,
          0 <= digit < 10 ->
          position < Znth digit counters 0 \/
          RadixBucketEnd histogram digit <= position) ->
      Znth position mixed_output None = None).

(** Sequential copy-back meaning: [working] agrees with the pass result on
    the copied prefix and with the pre-pass source on the remaining suffix. *)
Definition RadixCopyPrefix
    (source pass_output working : list Z) (copied : Z) : Prop :=
  (forall index,
      0 <= index < copied ->
      Znth index working 0 = Znth index pass_output 0) /\
  (forall index,
      copied <= index < Zlength source ->
      Znth index working 0 = Znth index source 0).
