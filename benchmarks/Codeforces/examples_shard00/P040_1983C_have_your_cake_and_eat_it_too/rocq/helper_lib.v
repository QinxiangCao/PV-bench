Require Import PVbench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CakeSumboolIf {P Q : Prop} {T : Type}
    (c : {P} + {Q}) (x y : T) : T :=
  match c with left _ => x | right _ => y end.

Local Notation "'if' c 'then' x 'else' y" :=
  (CakeSumboolIf c x y)
  (at level 200, c at level 200, x at level 200, y at level 79).

Import ListNotations.

Definition CakeSum (l : list Z) : Z := fold_right Z.add 0 l.

Definition CakeOrder (ord : list Z) : Prop :=
  ord = [0; 1; 2] \/ ord = [0; 2; 1] \/
  ord = [1; 0; 2] \/ ord = [1; 2; 0] \/
  ord = [2; 0; 1] \/ ord = [2; 1; 0].

Definition BoundLeft (bounds : list Z) (who : Z) : Z :=
  Znth (2 * who) bounds 0.

Definition BoundRight (bounds : list Z) (who : Z) : Z :=
  Znth (2 * who + 1) bounds 0.

Definition OrderedBy (ord bounds : list Z) : Prop :=
  CakeOrder ord /\
  BoundRight bounds (Znth 0 ord 0) < BoundLeft bounds (Znth 1 ord 0) /\
  BoundRight bounds (Znth 1 ord 0) < BoundLeft bounds (Znth 2 ord 0).

Definition TryOrderSpec
    (a b c ord : list Z) (out : option (list Z)) : Prop :=
  match out with
  | Some bounds => ValidCakeDivision a b c bounds /\ OrderedBy ord bounds
  | None => forall bounds, ValidCakeDivision a b c bounds -> ~ OrderedBy ord bounds
  end.

Definition SearchState
    (rows : list (list Z)) (who start pos need acc : Z) : Prop :=
  let row := Znth who rows [] in
  0 <= start /\ start <= pos /\ pos <= Zlength row /\
  acc = CakeSum (sublist start pos row) /\
  (forall q, start <= q < pos -> CakeSum (sublist start (q + 1) row) < need).

Definition SuffixSumState
    (rows : list (list Z)) (who start pos acc : Z) : Prop :=
  let row := Znth who rows [] in
  0 <= start /\ start <= pos /\ pos <= Zlength row /\
  acc = CakeSum (sublist start pos row).

Definition GreedyPrefixState
    (rows : list (list Z)) (ord : list Z) (need part pos : Z)
    (left right : list Z) : Prop :=
  CakeOrder ord /\ Zlength left = 3 /\ Zlength right = 3 /\
  0 <= part <= 2 /\ 0 <= pos <= Zlength (Znth 0 rows []) /\
  (forall k, 0 <= k < part ->
    let who := Znth k ord 0 in
    let lo := Znth who left 0 in
    let hi := Znth who right 0 in
    0 <= who < 3 /\ 0 <= lo /\ lo <= hi /\
    hi < Zlength (Znth who rows []) /\
    lo = if Z.eq_dec k 0 then 0
         else Znth (Znth (k - 1) ord 0) right 0 + 1 /\
    need <= CakeSum (sublist lo (hi + 1) (Znth who rows [])) /\
    (forall q, lo <= q < hi ->
      CakeSum (sublist lo (q + 1) (Znth who rows [])) < need)) /\
  pos = if Z.eq_dec part 0 then 0
        else Znth (Znth (part - 1) ord 0) right 0 + 1.

Definition OutputBounds (left right : list Z) : list Z :=
  [Znth 0 left 0 - 1; Znth 0 right 0 - 1;
   Znth 1 left 0 - 1; Znth 1 right 0 - 1;
   Znth 2 left 0 - 1; Znth 2 right 0 - 1].

Definition OrderAt (z : Z) (ord : list Z) : Prop :=
  (z = 0 /\ ord = [0; 1; 2]) \/
  (z = 1 /\ ord = [0; 2; 1]) \/
  (z = 2 /\ ord = [1; 0; 2]) \/
  (z = 3 /\ ord = [1; 2; 0]) \/
  (z = 4 /\ ord = [2; 0; 1]) \/
  (z = 5 /\ ord = [2; 1; 0]).

Definition OrderTable (table : list Z) : Prop :=
  table = [0; 1; 2; 0; 2; 1; 1; 0; 2; 1; 2; 0; 2; 0; 1; 2; 1; 0].

Definition OrderFor (z : Z) : list Z :=
  if Z.eq_dec z 0 then [0; 1; 2] else
  if Z.eq_dec z 1 then [0; 2; 1] else
  if Z.eq_dec z 2 then [1; 0; 2] else
  if Z.eq_dec z 3 then [1; 2; 0] else
  if Z.eq_dec z 4 then [2; 0; 1] else [2; 1; 0].

Definition FailedOrders (a b c : list Z) (z : Z) : Prop :=
  forall k, 0 <= k < z ->
    exists ord, OrderAt k ord /\ TryOrderSpec a b c ord None.

Definition SearchPrefixState
    (rows : list (list Z)) (who start pos need acc : Z) : Prop :=
  let row := Znth who rows [] in
  0 <= start /\ start <= pos /\ pos <= Zlength row /\
  acc = CakeSum (sublist start pos row) /\
  (forall q, start <= q < pos -> CakeSum (sublist start q row) < need).

Definition GreedyRawState
    (rows : list (list Z)) (ord : list Z) (need part pos : Z)
    (left right : list Z) : Prop :=
  CakeOrder ord /\ Zlength left = 3 /\ Zlength right = 3 /\
  0 <= part <= 2 /\ 0 <= pos <= Zlength (Znth 0 rows []) /\
  (forall k, 0 <= k < part ->
    let who := Znth k ord 0 in
    let lo := Znth who left 0 in
    let hi := Znth who right 0 in
    0 <= who < 3 /\ 1 <= lo /\ lo <= hi /\
    hi <= Zlength (Znth who rows []) /\
    lo = (if Z.eq_dec k 0 then 1
          else Znth (Znth (k - 1) ord 0) right 0 + 1) /\
    need <= CakeSum (sublist (lo - 1) hi (Znth who rows [])) /\
    (forall q, lo - 1 <= q < hi ->
      CakeSum (sublist (lo - 1) q (Znth who rows [])) < need)) /\
  pos = (if Z.eq_dec part 0 then 0
         else Znth (Znth (part - 1) ord 0) right 0).
