Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

#[export] Instance finite_bounded_pair (n m : Z) :
    Finite (fun p : Z * Z => 1 <= fst p < n + 1 /\ 1 <= snd p < m + 1) :=
  Finite_prod (fun i : Z => 1 <= i < n + 1) (fun j : Z => 1 <= j < m + 1).

Definition Pre (n m : Z) : Prop := 1 <= n <= 2000000 /\ 1 <= m <= 2000000.

Definition Spec (n m out : Z) : Prop :=
  out = #(fun p : Z * Z =>
    (1 <= fst p < n + 1 /\ 1 <= snd p < m + 1) /\
    (fst p + snd p | snd p * Z.gcd (fst p) (snd p))).

Require Import Coq.micromega.Lia.

Definition RCFiber (n m p q : Z) (ab : Z * Z) : Prop :=
  ((1 <= fst ab < n + 1 /\ 1 <= snd ab < m + 1) /\
   (fst ab + snd ab | snd ab * Z.gcd (fst ab) (snd ab))) /\
  fst ab / Z.gcd (fst ab) (snd ab) = p /\
  snd ab / Z.gcd (fst ab) (snd ab) = q.

#[export] Instance RC_fiber_finite n m p q : Finite (RCFiber n m p q) :=
  Finite_subset _ _.

Require Import Coq.Sorting.Permutation.
