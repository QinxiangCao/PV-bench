Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Import ListNotations.

Definition LowercaseLetter (c : Z) : Prop := 97 <= c <= 122.

Definition Pre (given : list (list Z)) : Prop :=
  1 <= Zlength given <= 100000 /\
  Forall (fun word =>
    0 < Zlength word <= 100000 /\
    Forall LowercaseLetter word) given.

Definition OccursContiguously (word text : list Z) : Prop :=
  exists before after, text = before ++ word ++ after.

Definition GoodRestoration (given : list (list Z)) (text : list Z) : Prop :=
  NoDup text /\
  (forall c,
    In c text <-> exists word, In word given /\ In c word) /\
  (forall word, In word given -> OccursContiguously word text).

Definition Spec (given : list (list Z)) (out : option (list Z)) : Prop :=
  match out with
  | Some text => GoodRestoration given text
  | None => forall text, ~ GoodRestoration given text
  end.

Require Import Coq.micromega.Lia.

Require Import Coq.micromega.Psatz.

From Coq Require Import Lia.
