
Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition IdentityRange (len : Z) (xs : list Z) : Prop :=
  Zlength xs = len /\
  forall i, 0 <= i < len -> Znth i xs 0 = i.

Definition TwiceModRange (n len : Z) (xs : list Z) : Prop :=
  Zlength xs = len /\
  forall i, 0 <= i < len -> Znth i xs 0 = (2 * i) mod n.
