Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.Relations.Relation_Operators Coq.Setoids.Setoid Coq.Classes.Morphisms SetsClass.SetsClass MaxMinLib.MaxMin AUXLib.MonotonicList.

Module Modern.
Definition StockTradeState := (Z * Z * Z)%type.

Definition StockTradeStep (ask bid buy sell : list Z) (max_stock wait : Z)
    (before after : StockTradeState) : Prop :=
  let '(previous_day, previous_stock, previous_profit) := before in
  let '(day, stock, profit) := after in
  (previous_day = 0 /\ previous_stock = 0 /\ previous_profit = 0 /\
    1 <= day /\ 1 <= stock <= Znth (day - 1) buy 0 /\
    stock <= max_stock /\ profit = - stock * Znth (day - 1) ask 0) \/
  (previous_day + wait < day /\
    ((1 <= stock - previous_stock <= Znth (day - 1) buy 0 /\
      stock <= max_stock /\
      profit = previous_profit - (stock - previous_stock) * Znth (day - 1) ask 0) \/
     (1 <= previous_stock - stock <= Znth (day - 1) sell 0 /\
      0 <= stock /\
      profit = previous_profit + (previous_stock - stock) * Znth (day - 1) bid 0))).

Definition StockTradingPath (ask bid buy sell : list Z) (max_stock wait : Z)
    (day stock profit : Z) : Prop :=
  exists first_day first_amount,
    1 <= first_day /\
    1 <= first_amount <= Znth (first_day - 1) buy 0 /\
    first_amount <= max_stock /\
    Relation_Operators.clos_refl_trans StockTradeState (StockTradeStep ask bid buy sell max_stock wait)
      (first_day, first_amount, - first_amount * Znth (first_day - 1) ask 0)
      (day, stock, profit).

Definition StockFeasiblePortfolio
    (ask bid buy sell : list Z) (max_stock wait horizon stock profit : Z) : Prop :=
  (stock = 0 /\ profit = 0) \/
  exists last_day, 1 <= last_day <= horizon /\
    StockTradingPath ask bid buy sell max_stock wait last_day stock profit.

Definition StockMaximumProfit (ask bid buy sell : list Z)
    (days max_stock wait answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : Z * Z => 0 <= fst candidate <= max_stock /\
       StockFeasiblePortfolio ask bid buy sell max_stock wait days
          (fst candidate) (snd candidate))
    (@snd Z Z) answer.
End Modern.

Export Modern.
