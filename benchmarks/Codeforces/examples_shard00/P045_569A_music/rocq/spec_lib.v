Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DownloadedAt (s q time : Z) : Z := s + (time * (q-1)) / q.

Definition CanFinishFrom (t s q start : Z) : Prop :=
  DownloadedAt s q (start + t) >= t.

Definition PlaybackStarts (t s q : Z) (starts : list Z) : Prop :=
  0 < Zlength starts /\ Znth 0 starts 0 = 0 /\
  (forall i, 0 <= i < Zlength starts-1 ->
    Znth (i+1) starts 0 - Znth i starts 0 = DownloadedAt s q (Znth (i+1) starts 0) /\
    ~ CanFinishFrom t s q (Znth i starts 0)) /\
  CanFinishFrom t s q (Znth (Zlength starts-1) starts 0).

Definition Pre (t s q : Z) : Prop := 2 <= q <= 10000 /\ 1 <= s < t /\ t <= 100000.

Definition Spec (t s q out : Z) : Prop := exists starts, PlaybackStarts t s q starts /\ out = Zlength starts.
