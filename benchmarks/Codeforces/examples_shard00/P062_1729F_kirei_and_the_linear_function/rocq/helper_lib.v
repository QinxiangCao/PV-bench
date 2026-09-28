Require Export PVbench.Codeforces.examples_shard00.P062_1729F_kirei_and_the_linear_function.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DigitPrefixValue (s : list Z) (i : Z) : Z :=
  sum_range 0 (i - 1) (fun j => Znth j s 48 - 48).

Definition DigitPrefixSums
    (s prefix_values : list Z) (endpoints_done : Z) : Prop :=
  forall j,
    0 <= j <= endpoints_done ->
    Znth j prefix_values 0 = DigitPrefixValue s j.

(** Canonical mixed-memory image while the local [pos] table is initialized.
    Rows before [rows_done] contain two [-1] sentinels; later rows remain
    undefined. *)
Definition pos_init_stage (rows_done : Z) : list (list (option Z)) :=
  map (fun r =>
    if Z_lt_dec r rows_done
    then Some (-1) :: Some (-1) :: nil
    else None :: None :: nil) (Zrange 0 9).

(** A one-based start [x] of a width-[w] window with residue [residue], among
    the first [starts_done] possible starts. *)
Definition WindowStart
    (s : list Z) (w starts_done residue x : Z) : Prop :=
  1 <= x <= starts_done /\
  x + w - 1 <= Zlength s /\
  DecimalSub s (x - 1) (x + w - 2) mod 9 = residue.

Definition FirstWindowStart
    (s : list Z) (w starts_done residue first : Z) : Prop :=
  (first = -1 /\
    forall x, ~ WindowStart s w starts_done residue x) \/
  (WindowStart s w starts_done residue first /\
    forall x, WindowStart s w starts_done residue x -> first <= x).

Definition SecondWindowStart
    (s : list Z) (w starts_done residue first second : Z) : Prop :=
  (second = -1 /\
    forall x,
      WindowStart s w starts_done residue x -> x = first) \/
  (WindowStart s w starts_done residue second /\
    second <> first /\
    forall x,
      WindowStart s w starts_done residue x ->
      x <> first -> second <= x).

(** Each row records the first two distinct one-based window starts for its
    residue.  Bounds and memory ownership stay in the C invariant. *)
Definition PositionsPrefix
    (s : list Z) (w starts_done : Z) (rows : list (list Z)) : Prop :=
  forall residue,
    0 <= residue < 9 ->
    let row := Znth residue rows nil in
    FirstWindowStart s w starts_done residue (Znth 0 row (-1)) /\
    SecondWindowStart s w starts_done residue
      (Znth 0 row (-1)) (Znth 1 row (-1)).

Definition PairLexLe (left right : Z * Z) : Prop :=
  fst left < fst right \/
  fst left = fst right /\ snd left <= snd right.

Definition PairFirstResidue (s : list Z) (w : Z) (p : Z * Z) : Z :=
  DecimalSub s (fst p - 1) (fst p + w - 2) mod 9.

Definition PrefixEligiblePair
    (s : list Z) (w : Z) (q : Z * Z * Z) (residues_done : Z)
    (p : Z * Z) : Prop :=
  QueryPair s w q p /\
  0 <= PairFirstResidue s w p < residues_done.

(** The best pair after considering first-window residues below
    [residues_done].  The large pair is the C implementation's private empty
    sentinel; it is not part of the public result. *)
Definition QueryBestPrefix
    (s : list Z) (w : Z) (q : Z * Z * Z)
    (residues_done best1 best2 : Z) : Prop :=
  (best1 = 1073741824 /\ best2 = 1073741824 /\
    forall candidate,
      ~ PrefixEligiblePair s w q residues_done candidate) \/
  min_value_of_subset PairLexLe
    (PrefixEligiblePair s w q residues_done)
    (fun candidate => candidate) (best1, best2).

(** The already written component arrays encode a result list satisfying the
    frozen public [Spec] for the corresponding query prefix. *)
Definition QueryOutputPrefix
    (w : Z) (s : list Z) (qs : list (Z * Z * Z)) (queries_done : Z)
    (out1 out2 : list Z) : Prop :=
  exists pairs,
    Spec w s (sublist 0 queries_done qs) pairs /\
    Zlength pairs = queries_done /\
    Zlength out1 = queries_done /\
    Zlength out2 = queries_done /\
    forall i,
      0 <= i < queries_done ->
      Znth i out1 0 = fst (Znth i pairs (0, 0)) /\
      Znth i out2 0 = snd (Znth i pairs (0, 0)).

(** Interpret the executable row-major [int pos[18]] as nine logical rows of
    two entries.  This is a representation bridge only: allocation length and
    memory ownership remain explicit in the C annotations. *)
Definition FlatPositionRows (flat : list Z) : list (list Z) :=
  map (fun residue =>
    Znth (2 * residue) flat (-1) ::
    Znth (2 * residue + 1) flat (-1) :: nil) (Zrange 0 9).

(** The first-two-starts invariant for the row-major executable table. *)
Definition FlatPositionsPrefix
    (s : list Z) (w starts_done : Z) (flat : list Z) : Prop :=
  PositionsPrefix s w starts_done (FlatPositionRows flat).

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.Logic.Classical_Prop.

Require Import Coq.ZArith.Zquot.
