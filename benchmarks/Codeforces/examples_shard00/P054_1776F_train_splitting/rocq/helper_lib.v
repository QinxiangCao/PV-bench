
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import GraphLib.graph_basic.

Require Import GraphLib.reachable.reachable_basic.

Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.

Local Open Scope Z_scope.

Definition Incident (x : Z) (p : Z * Z) : Prop :=
  fst p = x \/ snd p = x.

Definition EdgeDegree (x : Z) (e : list (Z * Z)) : Z :=
  Z.of_nat (length (filter
    (fun p => orb (Z.eqb (fst p) x) (Z.eqb (snd p) x)) e)).

Definition DegreePrefix (n : Z) (e : list (Z * Z)) (i : Z)
    (degrees : list Z) : Prop :=
  Zlength degrees = n /\
  forall x, 0 <= x < n ->
    Znth x degrees 0 = EdgeDegree x (sublist 0 i e).

Definition PivotPrefix (n : Z) (degrees : list Z) (i : Z) : Prop :=
  forall x, 0 <= x < i -> Znth x degrees 0 >= n - 1.

Definition PivotChoice (n : Z) (degrees : list Z) (pivot : Z) : Prop :=
  (0 <= pivot < n /\ Znth pivot degrees 0 < n - 1 /\
    PivotPrefix n degrees pivot) \/
  (pivot = -1 /\ PivotPrefix n degrees n).

Definition PivotColorPrefix (e : list (Z * Z)) (pivot i : Z)
    (labels : list Z) : Prop :=
  Zlength labels = i /\
  forall j, 0 <= j < i ->
    Znth j labels 0 =
      if orb (Z.eqb (fst (Znth j e (0,0))) pivot)
             (Z.eqb (snd (Znth j e (0,0))) pivot)
      then 1 else 2.

Definition IsFirstIncident (e : list (Z * Z)) (h : Z) : Prop :=
  0 <= h < Zlength e /\ Incident 0 (Znth h e (0,0)) /\
  forall j, 0 <= j < h -> ~ Incident 0 (Znth j e (0,0)).

Definition CompleteColorPrefix (e : list (Z * Z)) (i first : Z)
    (labels : list Z) : Prop :=
  Zlength labels = i /\
  ((first = 1 /\
      forall j, 0 <= j < i ->
        ~ Incident 0 (Znth j e (0,0)) /\ Znth j labels 0 = 3) \/
   (first = 0 /\ exists h,
      IsFirstIncident (sublist 0 i e) h /\
      forall j, 0 <= j < i ->
        Znth j labels 0 =
          if Z.eqb j h then 1
          else if orb (Z.eqb (fst (Znth j e (0,0))) 0)
                      (Z.eqb (snd (Znth j e (0,0))) 0)
               then 2 else 3)).
