Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition FishingScore (f cuts : list Z) (score : Z) : Prop :=
  2 <= Zlength cuts /\ Znth 0 cuts 0 = 0 /\
  Znth (Zlength cuts - 1) cuts 0 = Zlength f /\
  mono_inc cuts /\
  score = fold_right Z.add 0
    (Zmap_range (fun g =>
      g * fold_right Z.add 0
        (map (fun i => if Z.eqb (Znth i f 48) 49 then 1 else -1)
          (Zrange (Znth g cuts 0) (Znth (g + 1) cuts 0))))
      (Zlength cuts - 1)).

Definition Pre (k : Z) (f : list Z) : Prop :=
  2 <= Zlength f <= 200000 /\ 1 <= k <= 1000000000 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun c => c = 48 \/ c = 49) f.

Definition Spec (k : Z) (f : list Z) (out : Z) : Prop :=
  (out = -1 /\ forall candidate : list Z * Z,
    ~ (FishingScore f (fst candidate) (snd candidate) /\ snd candidate >= k)) \/
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      FishingScore f (fst candidate) (snd candidate) /\ snd candidate >= k)
    (fun candidate => Zlength (fst candidate) - 1) out.

Require Import Coq.micromega.Lia.

Require Import Coq.setoid_ring.Ring.

Require Import Coq.micromega.Psatz.
