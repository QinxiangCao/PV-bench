Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ValidDelegation (students : list (Z*Z)) (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength students) /\
  exists size, size > 0 /\ forall subject,
    (exists i, chosen i /\ fst (Znth i students (0,0)) = subject) ->
    #(fun i : Z => 0 <= i < Zlength students /\
      chosen i /\ fst (Znth i students (0,0)) = subject) = size.

Definition DelegationSkill (students : list (Z*Z)) (chosen : Z -> Prop) : Z :=
  sum (fun i : Z => 0 <= i < Zlength students /\ chosen i)
    (fun i => snd (Znth i students (0,0))).

Definition Pre (m : Z) (students : list (Z*Z)) : Prop := 1 <= Zlength students <= 100000 /\ 1 <= m <= 100000 /\
  Forall (fun p => 1 <= fst p <= m /\ -10000 <= snd p <= 10000) students.

Definition Spec (m : Z) (students : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (ValidDelegation students) (DelegationSkill students) 0 out.

(** Mathematical observations used by the C sweep.  They describe the
    sorted candidate sequence and the contribution of completed subject
    blocks; none of them executes the C loops. *)
Definition CandidateSubject (students : list (Z * Z)) (i : Z) : Z :=
  fst (Znth i students (0, 0)).

Definition CandidateSkill (students : list (Z * Z)) (i : Z) : Z :=
  snd (Znth i students (0, 0)).

Definition CandidatesSorted (students : list (Z * Z)) : Prop :=
  forall i j,
    0 <= i /\ i < j /\ j < Zlength students ->
    CandidateSubject students i < CandidateSubject students j \/
    (CandidateSubject students i = CandidateSubject students j /\
     CandidateSkill students j <= CandidateSkill students i).
