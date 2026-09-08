Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition NextNestedItem (previous next : list Z) : Prop :=
  next = previous ++ (1::nil) \/
  exists prefix last suffix,
    previous = prefix ++ last :: suffix /\
    next = prefix ++ (last+1)::nil /\
    Forall (fun x => x <> last) suffix.

Definition Pre (last_numbers : list Z) : Prop := 1 <= Zlength last_numbers <= 1000 /\
  Forall (fun x => 1 <= x <= Zlength last_numbers) last_numbers /\
  exists items, Zlength items = Zlength last_numbers /\ Znth 0 items nil = 1::nil /\
    (forall i, 0 <= i < Zlength items-1 -> NextNestedItem (Znth i items nil) (Znth (i+1) items nil)) /\
    Forall2
      (fun item last_number =>
        Znth (Zlength item - 1) item 0 = last_number)
      items last_numbers.

Definition Spec (last_numbers : list Z) (out : list (list Z)) : Prop :=
  Zlength out = Zlength last_numbers /\ Znth 0 out nil = 1::nil /\
  (forall i, 0 <= i < Zlength out-1 -> NextNestedItem (Znth i out nil) (Znth (i+1) out nil)) /\
  Forall2
    (fun item last_number =>
      Znth (Zlength item - 1) item 0 = last_number)
    out last_numbers.
