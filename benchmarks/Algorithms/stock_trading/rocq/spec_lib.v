Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StockTableShape
    (table : list (list Z)) (days max_stock : Z) : Prop :=
  Zlength table = days + 1 /\
  forall row, 0 <= row < days + 1 ->
    Zlength (Znth row table []) = max_stock + 1.
Definition StockInputsBounded
    (ask bid buy sell : list Z) (days max_stock : Z) : Prop :=
  Zlength ask = days /\
  Zlength bid = days /\
  Zlength buy = days /\
  Zlength sell = days /\
  1 <= days <= 990 /\
  1 <= max_stock <= 990 /\
  (forall day, 1 <= day <= days ->
     1 <= Znth (day - 1) bid 0 <= Znth (day - 1) ask 0 /\
     Znth (day - 1) ask 0 <= 1000 /\
     1 <= Znth (day - 1) buy 0 <= max_stock /\
     1 <= Znth (day - 1) sell 0 <= max_stock).
Inductive StockTradingHistory
    (ask bid buy sell : list Z) (max_stock wait : Z)
    : Z -> Z -> Z -> Prop :=
  | StockTradingHistory_first_buy :
      forall day amount,
        1 <= day ->
        1 <= amount <= Znth (day - 1) buy 0 ->
        amount <= max_stock ->
        StockTradingHistory ask bid buy sell max_stock wait
          day amount (- amount * Znth (day - 1) ask 0)
  | StockTradingHistory_buy :
      forall previous_day previous_stock previous_profit day amount,
        StockTradingHistory ask bid buy sell max_stock wait
          previous_day previous_stock previous_profit ->
        previous_day + wait < day ->
        1 <= amount <= Znth (day - 1) buy 0 ->
        previous_stock + amount <= max_stock ->
        StockTradingHistory ask bid buy sell max_stock wait
          day (previous_stock + amount)
          (previous_profit - amount * Znth (day - 1) ask 0)
  | StockTradingHistory_sell :
      forall previous_day previous_stock previous_profit day amount,
        StockTradingHistory ask bid buy sell max_stock wait
          previous_day previous_stock previous_profit ->
        previous_day + wait < day ->
        1 <= amount <= Znth (day - 1) sell 0 ->
        amount <= previous_stock ->
        StockTradingHistory ask bid buy sell max_stock wait
          day (previous_stock - amount)
          (previous_profit + amount * Znth (day - 1) bid 0).
Definition StockFeasiblePortfolio
    (ask bid buy sell : list Z) (max_stock wait horizon stock profit : Z) : Prop :=
  (stock = 0 /\ profit = 0) \/
  exists last_day,
    1 <= last_day <= horizon /\
    StockTradingHistory ask bid buy sell max_stock wait
      last_day stock profit.
Definition StockMaximumProfit
    (ask bid buy sell : list Z)
    (days max_stock wait answer : Z) : Prop :=
  exists stock,
    0 <= stock <= max_stock /\
    StockFeasiblePortfolio
      ask bid buy sell max_stock wait days stock answer /\
    forall stock' profit,
      0 <= stock' <= max_stock ->
      StockFeasiblePortfolio
        ask bid buy sell max_stock wait days stock' profit ->
      profit <= answer.
