Require Import PVbench.Codeforces.examples_shard00.P046_1082C_multi_subject_competition.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition SubjectBoundary (students : list (Z * Z)) (p : Z) : Prop :=
  0 <= p <= Zlength students /\
  (p = 0 \/ p = Zlength students \/
   CandidateSubject students (p - 1) <> CandidateSubject students p).

Definition SubjectBlockStart (students : list (Z * Z)) (p : Z) : Prop :=
  0 <= p < Zlength students /\
  (p = 0 \/
   CandidateSubject students (p - 1) <> CandidateSubject students p).

Definition SkillSum (students : list (Z * Z)) (lo hi : Z) : Z :=
  fold_right Z.add 0 (map snd (sublist lo hi students)).

Definition SubjectHasK
    (students : list (Z * Z)) (start k : Z) : Prop :=
  SubjectBlockStart students start /\
  1 <= k /\ start + k <= Zlength students /\
  forall t, start <= t < start + k ->
    CandidateSubject students t = CandidateSubject students start.

Definition SubjectContribution
    (students : list (Z * Z)) (start k : Z) : Z :=
  if prop_dec (SubjectHasK students start k)
  then Z.max 0 (SkillSum students start (start + k))
  else 0.

Definition CompletedContribution
    (students : list (Z * Z)) (processed k : Z) : Z :=
  sum
    (fun start : Z =>
       0 <= start < processed /\ SubjectBlockStart students start)
    (fun start => SubjectContribution students start k).

Definition CompetitionOuterState
    (students : list (Z * Z)) (processed : Z) (totals : list Z) : Prop :=
  SubjectBoundary students processed /\
  Zlength totals = Zlength students + 1 /\
  Znth 0 totals 0 = 0 /\
  forall k, 1 <= k <= Zlength students ->
    Znth k totals 0 = CompletedContribution students processed k.

Definition CompetitionInnerState
    (students : list (Z * Z)) (start done prefix : Z)
    (totals : list Z) : Prop :=
  0 <= start /\ start <= done /\ done <= Zlength students /\
  SubjectBoundary students start /\
  (start < done ->
   forall t, start <= t < done ->
     CandidateSubject students t = CandidateSubject students start) /\
  prefix = SkillSum students start done /\
  Zlength totals = Zlength students + 1 /\
  Znth 0 totals 0 = 0 /\
  forall k, 1 <= k <= Zlength students ->
    Znth k totals 0 =
      CompletedContribution students start k +
      (if prop_dec (1 <= k <= done - start)
       then SubjectContribution students start k
       else 0).

Definition CompetitionAnswerPrefix
    (totals : list Z) (n done answer : Z) : Prop :=
  Zlength totals = n + 1 /\ 0 <= done <= n /\
  max_value_of_subset_with_default Z.le
    (fun k : Z => 1 <= k <= done)
    (fun k => Znth k totals 0) 0 answer.
