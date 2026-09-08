Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Require Import AUXLib.ListLib.

Local Open Scope Z_scope.

Definition Pre (k : Z) (a : list Z) : Prop :=
  1 <= k <= 200000 /\
  1 <= Zlength a <= 200000 /\
  Forall (fun x => -1000000000 <= x <= 1000000000) a.


Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  out = #(fun q : Z * (Z * Z) =>
    (0 <= fst q < Zlength a /\
     0 <= fst (snd q) < Zlength a /\
     0 <= snd (snd q) < Zlength a) /\
    fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
    Znth (fst (snd q)) a 0 = Znth (fst q) a 0 * k /\
    Znth (snd (snd q)) a 0 = Znth (fst (snd q)) a 0 * k).
