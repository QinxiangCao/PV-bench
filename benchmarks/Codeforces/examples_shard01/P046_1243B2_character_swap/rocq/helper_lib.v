Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P046_1243B2_character_swap.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition CountedPrefix
    (s t : list Z) (i : Z) (counts : list Z) : Prop :=
  Zlength counts = 26 /\
  forall c, 0 <= c < 26 ->
    Znth c counts 0 =
      Z.of_nat
        (count_occ Z.eq_dec
          (sublist 0 i s ++ sublist 0 i t) (97 + c)).

Definition CountsEvenBefore (counts : list Z) (bound : Z) : Prop :=
  forall c, 0 <= c < bound -> Z.modulo (Znth c counts 0) 2 = 0.

Definition CombinedEven (s t : list Z) : Prop :=
  forall c, 0 <= c < 26 ->
    Z.modulo
      (Z.of_nat (count_occ Z.eq_dec (s ++ t) (97 + c))) 2 = 0.

Definition CombinedOddAt (s t : list Z) (c : Z) : Prop :=
  0 <= c < 26 /\
  Z.modulo
    (Z.of_nat (count_occ Z.eq_dec (s ++ t) (97 + c))) 2 = 1.

Definition SwapTrace
    (s0 t0 s t : list Z) (ops : list (Z * Z)) : Prop :=
  exists states : list (list Z * list Z),
    Zlength states = Zlength ops + 1 /\
    Znth 0 states ([], []) = (s0, t0) /\
    (forall q, 0 <= q < Zlength ops ->
      CrossSwap
        (Znth q states ([], []))
        (Znth (q + 1) states ([], []))
        (Znth q ops (0, 0))) /\
    Znth (Zlength ops) states ([], []) = (s, t).

Definition PrefixEqual (s t : list Z) (i : Z) : Prop :=
  forall k, 0 <= k < i -> Znth k s 0 = Znth k t 0.

Definition NoValueInRange
    (l : list Z) (value lo hi : Z) : Prop :=
  forall k, lo <= k < hi -> Znth k l 0 <> value.

Definition OperationLists
    (ops : list (Z * Z)) (is js : list Z) : Prop :=
  Zlength is = Zlength ops /\
  Zlength js = Zlength ops /\
  (forall q, 0 <= q < Zlength ops ->
    Znth q is 0 = fst (Znth q ops (0, 0)) + 1 /\
    Znth q js 0 = snd (Znth q ops (0, 0)) + 1).

Definition RepairState
    (source target s t : list Z) (i : Z)
    (ops : list (Z * Z)) : Prop :=
  Zlength s = Zlength source /\
  Zlength t = Zlength target /\
  PrefixEqual s t i /\
  Permutation (source ++ target) (s ++ t) /\
  CombinedEven s t /\
  SwapTrace source target s t ops /\
  0 <= Zlength ops <= 2 * i.
