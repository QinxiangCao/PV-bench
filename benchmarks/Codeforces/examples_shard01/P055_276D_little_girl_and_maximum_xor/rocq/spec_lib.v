(* Codeforces 276/D - Little Girl and Maximum XOR: the largest value of a xor b
   over pairs with l <= a <= b <= r. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* 1 <= l <= r <= 10^18. *)
Definition Pre (l r : Z) : Prop :=
  (* Stated explicitly in the P055 solver Require, which therefore omits the
     Pre(...) call: 1 <= l <= r /\ r <= Z.pow 10 18. *)
  True.

(* out = max { a xor b : l <= a <= b <= r }. *)
Definition Spec (l r out : Z) : Prop :=
  max_value_of_subset Z.le (fun v => exists a b, l <= a <= b /\ b <= r /\ v = Z.lxor a b) (fun x => x) out.
