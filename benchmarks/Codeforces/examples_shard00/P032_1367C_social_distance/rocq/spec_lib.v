Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition RespectsDistance (k : Z) (occupied : Z -> Prop) : Prop :=
  forall i j, occupied i -> occupied j -> i <> j -> Z.abs (i - j) > k.

Definition AdditionalTables (s : list Z) (k : Z) (extra : Z -> Prop) : Prop :=
  (forall i, extra i -> 0 <= i < Zlength s /\ Znth i s 48 = 48) /\
  RespectsDistance k
    (fun i => (0 <= i < Zlength s /\ Znth i s 48 = 49) \/ extra i).

Definition Pre (k : Z) (s : list Z) : Prop :=
  1 <= k <= Zlength s /\ Zlength s <= 200000 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun c => c = 48 \/ c = 49) s /\
  RespectsDistance k (fun i => 0 <= i < Zlength s /\ Znth i s 48 = 49).

Definition Spec (k : Z) (s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      AdditionalTables s k (fst candidate) /\
      snd candidate = #(fun i : Z =>
        0 <= i < Zlength s /\ fst candidate i))
    snd out.
