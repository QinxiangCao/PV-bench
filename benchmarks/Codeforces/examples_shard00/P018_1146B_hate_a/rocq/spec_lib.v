Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Local Open Scope Z_scope.

Definition GeneratesHatedAString (source given : list Z) : Prop :=
  given = source ++ filter (fun c => negb (Z.eqb c 97)) source.

Definition Pre (given : list Z) : Prop :=
  1 <= Zlength given <= 100000 /\
  Forall (fun c => 97 <= c <= 122) given.

Definition Spec (given : list Z) (out : option (list Z)) : Prop :=
  (exists source, out = Some source /\ GeneratesHatedAString source given) \/
  (out = None /\ forall source, ~ GeneratesHatedAString source given).
