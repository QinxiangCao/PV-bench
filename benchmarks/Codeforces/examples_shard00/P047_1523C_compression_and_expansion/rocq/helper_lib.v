
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CurrentItem (items : list (list Z)) (count : Z)
    (active : list Z) : Prop :=
  (count = 0 /\ active = nil) \/
  (0 < count /\ active = Znth (count - 1) items nil).

Definition PopTarget (active target : list Z) (x : Z) : Prop :=
  exists prefix last suffix,
    active = prefix ++ last :: suffix /\
    target = prefix ++ (last + 1) :: nil /\
    x = last + 1 /\
    Forall (fun y => y <> last) suffix.

Definition FlatPrefix (items : list (list Z)) (count : Z)
    (flat_data : list Z) : Prop :=
  flat_data = concat (sublist 0 count items).

Definition LengthsPrefix (items : list (list Z)) (count : Z)
    (lengths_data : list Z) : Prop :=
  Zlength lengths_data = count /\
  forall i, 0 <= i < count ->
    Znth i lengths_data 0 = Zlength (Znth i items nil).

Definition BoundedItem (bound : Z) (item : list Z) : Prop :=
  Forall (fun value => 1 <= value <= bound) item.
