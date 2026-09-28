Require Export PVbench.Codeforces.examples_shard00.P073_400E_inna_and_binary_logic.rocq.spec_lib.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.

Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Auxiliary mathematical summaries; the specification above is unchanged. *)
Definition P073AllOn (b : Z) (xs : list Z) : bool :=
  forallb (fun x => Z.testbit x b) xs.

Definition P073Indicator (p : bool) : Z := if p then 1 else 0.

Definition P073Prefix (b : Z) (xs : list Z) : Z :=
  fold_right Z.add 0
    (map (fun k => P073Indicator (P073AllOn b (sublist 0 k xs)))
      (Zrange 1 (Zlength xs + 1))).

Definition P073Suffix (b : Z) (xs : list Z) : Z :=
  fold_right Z.add 0
    (map (fun k => P073Indicator
      (P073AllOn b (sublist (Zlength xs - k) (Zlength xs) xs)))
      (Zrange 1 (Zlength xs + 1))).

Definition P073Count (b : Z) (xs : list Z) : Z :=
  fold_right Z.add 0
    (map (fun l => fold_right Z.add 0
      (map (fun r => P073Indicator (P073AllOn b (sublist l (r+1) xs)))
        (Zrange l (Zlength xs)))) (Zrange 0 (Zlength xs))).

Definition P073Summary (b : Z) (xs : list Z) (p s c : Z) : Prop :=
  p = P073Prefix b xs /\ s = P073Suffix b xs /\ c = P073Count b xs.

(* A mathematical binary partition, independent of array contents. *)
Inductive P073Desc : Z -> Z -> Z -> Z -> Z -> Z -> Prop :=
| P073Desc_here : forall v l r, P073Desc v l r v l r
| P073Desc_left : forall v l r w lo hi,
    r-l > 1 -> P073Desc (2*v) l ((l+r)/2) w lo hi ->
    P073Desc v l r w lo hi
| P073Desc_right : forall v l r w lo hi,
    r-l > 1 -> P073Desc (2*v+1) ((l+r)/2) r w lo hi ->
    P073Desc v l r w lo hi.

Definition P073Layout (n v l r : Z) : Prop :=
  forall w lo hi, P073Desc v l r w lo hi ->
    0 < w < 4*n /\ 0 <= lo < hi /\ hi <= n.

Definition P073Tree (n v l r : Z) (xs pr su ct ln : list Z) : Prop :=
  forall w lo hi, P073Desc v l r w lo hi ->
    Znth w ln 0 = hi-lo /\
    forall b, 0 <= b < 17 ->
      P073Summary b (sublist lo hi xs)
        (Znth (b*4*n+w) pr 0) (Znth (b*4*n+w) su 0)
        (Znth (b*4*n+w) ct 0).

Definition P073ZeroTree (n v l r : Z) (pr su ct ln : list Z) : Prop :=
  forall w lo hi, P073Desc v l r w lo hi ->
    Znth w ln 0 = 0 /\
    forall b, 0 <= b < 17 ->
      Znth (b*4*n+w) pr 0 = 0 /\ Znth (b*4*n+w) su 0 = 0 /\
      Znth (b*4*n+w) ct 0 = 0.

Definition P073OutsideTree (n v l r : Z)
    (oldpr oldsu oldct oldln pr su ct ln : list Z) : Prop :=
  (forall w, 0 <= w < 4*n ->
    (forall lo hi, ~ P073Desc v l r w lo hi) ->
    Znth w ln 0 = Znth w oldln 0) /\
  (forall w b, 0 <= w < 4*n -> 0 <= b < 17 ->
    (forall lo hi, ~ P073Desc v l r w lo hi) ->
    Znth (b*4*n+w) pr 0 = Znth (b*4*n+w) oldpr 0 /\
    Znth (b*4*n+w) su 0 = Znth (b*4*n+w) oldsu 0 /\
    Znth (b*4*n+w) ct 0 = Znth (b*4*n+w) oldct 0).

Definition P073NodePrefix (n v bits : Z) (xs pr su ct : list Z) : Prop :=
  forall b, 0 <= b < bits ->
    P073Summary b xs (Znth (b*4*n+v) pr 0)
      (Znth (b*4*n+v) su 0) (Znth (b*4*n+v) ct 0).

Definition P073NodeFrame (n v bits : Z)
    (oldpr oldsu oldct pr su ct : list Z) : Prop :=
  forall b w, 0 <= b < 17 -> 0 <= w < 4*n ->
    (w <> v \/ bits <= b) ->
    Znth (b*4*n+w) pr 0 = Znth (b*4*n+w) oldpr 0 /\
    Znth (b*4*n+w) su 0 = Znth (b*4*n+w) oldsu 0 /\
    Znth (b*4*n+w) ct 0 = Znth (b*4*n+w) oldct 0.

Definition P073BufferBounds (n : Z) (pr su ct ln : list Z) : Prop :=
  (forall k, 0 <= k < 68*n ->
    0 <= Znth k pr 0 <= n /\ 0 <= Znth k su 0 <= n /\
    0 <= Znth k ct 0 <= n*(n+1)/2) /\
  (forall k, 0 <= k < 4*n -> 0 <= Znth k ln 0 <= n).

Definition P073Weighted (xs : list Z) (bits : Z) : Z :=
  fold_right Z.add 0
    (map (fun b => P073Count b xs * 2^b) (Zrange 0 bits)).

Definition P073History (initial : list Z) (updates : list (Z*Z))
    (done : Z) (current output : list Z) : Prop :=
  exists states,
    Zlength states = done+1 /\ Znth 0 states nil = initial /\
    Znth done states nil = current /\
    (forall i, 0 <= i < done ->
      Znth (i+1) states nil = ApplyPointUpdate (Znth i states nil)
        (Znth i updates (0,0))) /\
    Zlength output = done /\
    (forall i, 0 <= i < done ->
      Znth i output 0 = AndExerciseSum (Znth (i+1) states nil)).

Require Import Coq.micromega.Psatz.

Require Import Coq.micromega.Lia.
