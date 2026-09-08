Require Import PVbench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.

Local Open Scope Z_scope.

Definition ShirtTrace (score : Z) (values : list Z) : Prop :=
  Zlength values = 26 /\
  Znth 0 values 0 = (score / 50) mod 475 /\
  forall i, 0 <= i < 25 ->
    Znth (i + 1) values 0 = (Znth i values 0 * 96 + 42) mod 475.

Definition NoShirtSelection (score place : Z) : Prop :=
  ~ ShirtSelection score place.

Definition ShirtScanState
    (score place scanned current : Z) : Prop :=
  exists values,
    ShirtTrace score values /\
    0 <= scanned <= 25 /\
    current = Znth scanned values 0 /\
    (forall i, 1 <= i <= scanned -> place <> 26 + Znth i values 0).

Definition AlignmentSearch (x y score : Z) : Prop :=
  y <= score /\
  forall candidate,
    y <= candidate < score -> (candidate - x) mod 50 <> 0.

Definition CandidateSearch (place x y score : Z) : Prop :=
  y <= score /\
  (score - x) mod 50 = 0 /\
  forall candidate,
    y <= candidate < score ->
    (candidate - x) mod 50 = 0 ->
    NoShirtSelection candidate place.

Definition FirstWinningCandidate (place x y score : Z) : Prop :=
  CandidateSearch place x y score /\ ShirtSelection score place.
