Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.
(** The sum [1 + ... + k].  This is the mathematical quantity tracked by
    the first loop, rather than a model of that loop's control flow. *)
Definition triangular (k : Z) : Z := k * (k + 1) / 2.

(** A concrete prefix [1; 2; ...; i], used while the output buffer is being
    initialized. *)
Definition CandyPrefix (i : Z) (xs : list Z) : Prop :=
  Zlength xs = i /\
  forall j, 0 <= j < i -> Znth j xs 0 = j + 1.

(** The final greedy construction: [1; ...; k-1] followed by the remaining
    candies.  This describes the constructed mathematical list independently
    of the implementation's two loops. *)
Definition GreedyCandyPlan (n k : Z) (xs : list Z) : Prop :=
  Zlength xs = k /\
  (forall j, 0 <= j < k - 1 -> Znth j xs 0 = j + 1) /\
  Znth (k - 1) xs 0 = k + (n - triangular k).
