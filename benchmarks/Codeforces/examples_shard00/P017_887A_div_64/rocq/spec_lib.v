Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ChosenBinaryDigits (s : list Z) (indices digits : list Z) : Prop :=
  0 < Zlength indices /\
  Forall2
    (fun index digit =>
      0 <= index < Zlength s /\ digit = Znth index s 0)
    indices digits /\
  mono_inc indices.

Definition BinaryValue (digits : list Z) : Z :=
  fold_left (fun value character => 2 * value + (character - 48)) digits 0.

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 100 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun character => character = 48 \/ character = 49) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists indices digits,
    ChosenBinaryDigits s indices digits /\
    BinaryValue digits > 0 /\
    (64 | BinaryValue digits)).

Require Import Coq.micromega.Lia.
