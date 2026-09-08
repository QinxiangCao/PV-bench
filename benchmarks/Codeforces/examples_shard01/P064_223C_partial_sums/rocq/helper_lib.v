Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition ModPower (base exponent result : Z) : Prop :=
  result = (base ^ exponent) mod 1000000007.

Definition PowerLoopState
    (original_base original_exponent accumulator current_base
     remaining_exponent : Z) : Prop :=
  (accumulator * (current_base ^ remaining_exponent)) mod 1000000007 =
  (original_base ^ original_exponent) mod 1000000007.

Definition IdentityPrefix (values written : list Z) : Prop :=
  forall i, 0 <= i < Zlength written ->
    Znth i written 0 = Znth i values 0.

Definition CoefficientPrefix (k : Z) (coefficients : list Z) : Prop :=
  (0 < Zlength coefficients -> Znth 0 coefficients 0 = 1) /\
  forall d, 1 <= d < Zlength coefficients ->
    Znth d coefficients 0 =
      ((((Znth (d - 1) coefficients 0) mod 1000000007) *
         ((k - 1 + d) mod 1000000007)) mod 1000000007 *
        ((d ^ 1000000005) mod 1000000007)) mod 1000000007.

Definition ConvolutionPrefix
    (values coefficients written : list Z) : Prop :=
  forall i, 0 <= i < Zlength written ->
    Znth i written 0 =
      (sum_range 0 i
         (fun j =>
            Znth (i - j) coefficients 0 *
            ((Znth j values 0) mod 1000000007))) mod 1000000007.

Definition ConvolutionAccumulator
    (values coefficients : list Z) (output_index scanned accumulator : Z) : Prop :=
  accumulator =
    (sum_range 0 (scanned - 1)
       (fun j =>
          Znth (output_index - j) coefficients 0 *
          ((Znth j values 0) mod 1000000007))) mod 1000000007.
