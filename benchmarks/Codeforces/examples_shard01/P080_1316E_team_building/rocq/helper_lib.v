Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition BitCount (v count : Z) : Prop :=
  count = fold_right Z.add 0
    (map (fun bit => if Z.testbit v bit then 1 else 0) (Zrange 0 32)).

(* The heap sort moves audience values and their original-person indexes as
   inseparable pairs. *)

Definition PeoplePermutation
    (audience order audience' order' : list Z) : Prop :=
  Permutation (combine audience order) (combine audience' order').

Definition PeopleHeapParentsFrom
    (audience : list Z) (lo hi : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    Znth child audience 0 <= Znth ((child - 1) / 2) audience 0.

Definition PeopleHeapOrderedExceptAt
    (audience : list Z) (lo hi bad : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    (child - 1) / 2 <> bad ->
    Znth child audience 0 <= Znth ((child - 1) / 2) audience 0.

Definition BitCountProgress
    (original remaining count : Z) : Prop :=
  exists consumed,
    0 <= consumed <= 32 /\
    remaining = Z.shiftr original consumed /\
    count = fold_right Z.add 0
      (map (fun bit => if Z.testbit original bit then 1 else 0)
           (Zrange 0 consumed)).

Definition PeopleSiftProgress
    (audience0 order0 audience order : list Z)
    (root0 root hi n : Z) : Prop :=
  PeoplePermutation audience0 order0 audience order /\
  sublist (hi + 1) n audience = sublist (hi + 1) n audience0 /\
  sublist (hi + 1) n order = sublist (hi + 1) n order0 /\
  PeopleHeapOrderedExceptAt audience root0 hi root /\
  (root = root0 \/
   ((2 * root + 1 <= hi ->
       Znth (2 * root + 1) audience 0 <=
       Znth ((root - 1) / 2) audience 0) /\
    (2 * root + 2 <= hi ->
       Znth (2 * root + 2) audience 0 <=
       Znth ((root - 1) / 2) audience 0))).

Definition PeopleSelectedLargerChild
    (audience : list Z) (root hi child : Z) : Prop :=
  (child = 2 * root + 1 \/ child = 2 * root + 2) /\
  child <= hi /\
  (2 * root + 1 <= hi ->
     Znth (2 * root + 1) audience 0 <= Znth child audience 0) /\
  (2 * root + 2 <= hi ->
     Znth (2 * root + 2) audience 0 <= Znth child audience 0).

Definition PeopleHeapBuildState
    (audience0 order0 audience order : list Z) (root n : Z) : Prop :=
  PeoplePermutation audience0 order0 audience order /\
  PeopleHeapParentsFrom audience (root + 1) (n - 1).

Definition PeopleHeapSortState
    (audience0 order0 audience order : list Z) (hi : Z) : Prop :=
  PeoplePermutation audience0 order0 audience order /\
  PeopleHeapParentsFrom audience 0 hi /\
  ListLib.increasing (sublist (hi + 1) (Zlength audience) audience) /\
  (forall left right,
     0 <= left <= hi ->
     hi < right < Zlength audience ->
     Znth left audience 0 <= Znth right audience 0).

Definition SortedPeopleState
    (audience0 order0 audience order : list Z) : Prop :=
  Zlength audience = Zlength audience0 /\
  Zlength order = Zlength order0 /\
  PeoplePermutation audience0 order0 audience order /\
  ListLib.increasing audience /\
  (forall q,
     0 <= q < Zlength order ->
     0 <= Znth q order 0 < Zlength audience0 /\
     Znth q audience 0 = Znth (Znth q order 0) audience0 0).

Definition TeamNegInf : Z := -(2 ^ 60).

Definition AllTeamNegInf (values : list Z) : Prop :=
  Forall (fun value => value = TeamNegInf) values.

Definition ProcessedPerson
    (sorted_order : list Z) (processed person : Z) : Prop :=
  exists step,
    0 <= step < processed /\
    person = Znth (Zlength sorted_order - 1 - step) sorted_order 0.

Definition AssignmentsMatchMask
    (positions mask : Z) (assignments : list (Z * Z)) : Prop :=
  NoDup (map fst assignments) /\
  (forall role,
     0 <= role < positions ->
     (Z.testbit mask role = true <->
      exists person, In (role, person) assignments)).

Definition TeamPrefixChoice
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask score : Z)
    : Prop :=
  0 <= mask < 2 ^ positions /\
  exists assignments audience_people,
    AssignmentsMatchMask positions mask assignments /\
    NoDup (map snd assignments ++ audience_people) /\
    Forall (ProcessedPerson sorted_order processed)
      (map snd assignments ++ audience_people) /\
    Zlength audience_people =
      Z.min audience_limit (processed - Zlength assignments) /\
    score =
      fold_right Z.add 0
        (map
          (fun assignment =>
             Znth (fst assignment)
               (Znth (snd assignment) skill []) 0)
          assignments) +
      fold_right Z.add 0
        (map (fun person => Znth person audience 0) audience_people).

Definition TeamDPCell
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask value : Z)
    : Prop :=
  max_value_of_subset Z.le
    (TeamPrefixChoice audience skill sorted_order
      positions audience_limit processed mask)
    (fun score => score) value \/
  (value = TeamNegInf /\
   forall score,
     ~ TeamPrefixChoice audience skill sorted_order
         positions audience_limit processed mask score).

Definition TeamDPTable
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed : Z)
    (values : list Z) : Prop :=
  forall mask,
    0 <= mask < 2 ^ positions ->
    TeamDPCell audience skill sorted_order positions audience_limit
      processed mask (Znth mask values TeamNegInf).

Definition TeamTransitionCandidate
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values : list Z)
    (source_limit target score : Z) : Prop :=
  exists source source_score,
    0 <= source < source_limit /\
    source_score = Znth source old_values TeamNegInf /\
    source_score <> TeamNegInf /\
    ((target = source /\ score = source_score) \/
     (exists used,
        BitCount source used /\
        processed - used < audience_limit /\
        target = source /\
        score = source_score +
          Znth (Zlength sorted_audience - 1 - processed)
            sorted_audience 0) \/
     (exists role,
        0 <= role < positions /\
        Z.testbit source role = false /\
        target = Z.lor source (2 ^ role) /\
        score = source_score +
          Znth role
            (Znth
              (Znth (Zlength sorted_order - 1 - processed)
                sorted_order 0)
              skill []) 0)).

Definition TeamNextRowProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source_limit : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (TeamTransitionCandidate sorted_audience sorted_order skill
         positions audience_limit processed old_values source_limit target)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source_limit
            target score)).

Definition TeamCurrentSourceCandidate
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values : list Z)
    (source roles_scanned target score : Z) : Prop :=
  let source_score := Znth source old_values TeamNegInf in
  source_score <> TeamNegInf /\
  ((target = source /\ score = source_score) \/
   (exists used,
      BitCount source used /\
      processed - used < audience_limit /\
      target = source /\
      score = source_score +
        Znth (Zlength sorted_audience - 1 - processed)
          sorted_audience 0) \/
   (exists role,
      0 <= role < roles_scanned /\
      Z.testbit source role = false /\
      target = Z.lor source (2 ^ role) /\
      score = source_score +
        Znth role
          (Znth
            (Znth (Zlength sorted_order - 1 - processed)
              sorted_order 0)
            skill []) 0)).

Definition TeamRoleUpdateProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source roles_scanned : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (fun score =>
          TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source target score \/
          TeamCurrentSourceCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source roles_scanned
            target score)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ (TeamTransitionCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source target score \/
           TeamCurrentSourceCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source roles_scanned
             target score))).

Definition TeamCopyPrefix
    (source destination : list Z) (copied : Z) : Prop :=
  forall mask,
    0 <= mask < copied ->
    Znth mask destination TeamNegInf = Znth mask source TeamNegInf.

(* Revision-2 bounded DP semantics.  The revision is additive because the
   earlier declarations are part of the frozen formal surface. *)

Definition BoundedAssignmentsMatchMask
    (positions mask : Z) (assignments : list (Z * Z)) : Prop :=
  AssignmentsMatchMask positions mask assignments /\
  Forall (fun assignment => 0 <= fst assignment < positions) assignments.

Definition BoundedTeamPrefixChoice
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask score : Z)
    : Prop :=
  0 <= mask < 2 ^ positions /\
  exists assignments audience_people,
    BoundedAssignmentsMatchMask positions mask assignments /\
    NoDup (map snd assignments ++ audience_people) /\
    Forall (ProcessedPerson sorted_order processed)
      (map snd assignments ++ audience_people) /\
    Zlength audience_people =
      Z.min audience_limit (processed - Zlength assignments) /\
    score =
      fold_right Z.add 0
        (map
          (fun assignment =>
             Znth (fst assignment)
               (Znth (snd assignment) skill []) 0)
          assignments) +
      fold_right Z.add 0
        (map (fun person => Znth person audience 0) audience_people).

Definition BoundedTeamDPCell
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask value : Z)
    : Prop :=
  max_value_of_subset Z.le
    (BoundedTeamPrefixChoice audience skill sorted_order
      positions audience_limit processed mask)
    (fun score => score) value \/
  (value = TeamNegInf /\
   forall score,
     ~ BoundedTeamPrefixChoice audience skill sorted_order
         positions audience_limit processed mask score).

Definition BoundedTeamDPTable
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed : Z)
    (values : list Z) : Prop :=
  forall mask,
    0 <= mask < 2 ^ positions ->
    BoundedTeamDPCell audience skill sorted_order positions audience_limit
      processed mask (Znth mask values TeamNegInf).

Definition BoundedTeamNextRowProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source_limit : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (TeamTransitionCandidate sorted_audience sorted_order skill
         positions audience_limit processed old_values source_limit target)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source_limit
            target score)).

Definition BoundedTeamRoleUpdateProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source roles_scanned : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (fun score =>
          TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source target score \/
          TeamCurrentSourceCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source roles_scanned
            target score)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ (TeamTransitionCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source target score \/
           TeamCurrentSourceCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source roles_scanned
             target score))).

Definition BoundedTeamCopyPrefix
    (source destination : list Z) (copied : Z) : Prop :=
  forall mask,
    0 <= mask < copied ->
    Znth mask destination TeamNegInf = Znth mask source TeamNegInf.
