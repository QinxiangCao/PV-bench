Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The contribution of the decimal places 10^0, ..., 10^(k-1).
   [next] is the first place value not yet included. *)
Definition DecimalPlacePrefix (x next total : Z) : Prop :=
  exists k,
    0 <= k <= 10 /\
    next = Z.pow 10 k /\
    total = sum_range 0 (k - 1) (fun d => x / Z.pow 10 d).

(* Once the next decimal place is larger than [x], every remaining quotient
   is zero, so the prefix is the complete digit-change count up to [x]. *)
Definition DecimalPrefixTotal (x total : Z) : Prop :=
  exists next,
    x < next /\ DecimalPlacePrefix x next total.
