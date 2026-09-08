Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition GcdValue (a b : Z) : Z := Z.gcd a b.

Definition OutputPrefix (a out : list Z) (budget : Z) : Prop :=
  Zlength out = Zlength a /\
  Forall (fun x => x <> 0) out /\
  (fold_right Z.add 0)
    (map (fun q => fst q * snd q) (combine a out)) = 0 /\
  (fold_right Z.add 0) (map Z.abs out) <=
    10000 * Zlength out + budget.
