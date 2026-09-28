Require Export PVbench.Algorithms.stock_trading.rocq.spec_lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import Coq.Relations.Relation_Operators Coq.Setoids.Setoid Coq.Classes.Morphisms SetsClass.SetsClass MaxMinLib.MaxMin AUXLib.MonotonicList.

Module Legacy.
Definition STOCK_NEG_INF : Z := -1000000000.

Definition StockInitialCell (day stock : Z) : Z :=
  if Z.eq_dec day 0 then
    if Z.eq_dec stock 0 then 0 else STOCK_NEG_INF
  else STOCK_NEG_INF.

Definition StockSellScore
    (table : list (list Z)) (source price stock : Z) : Z :=
  Znth stock (Znth source table []) 0 + stock * price.

Definition StockBuyScore
    (table : list (list Z)) (source price stock : Z) : Z :=
  Znth stock (Znth source table []) 0 + stock * price.

Definition StockFiniteTableIndex
    (table : list (list Z)) (source stock : Z) : Prop :=
  0 <= stock /\
  stock < Zlength (Znth source table []) /\
  Znth stock (Znth source table []) 0 <> STOCK_NEG_INF.

Definition StockFiniteIndexInWindow
    (table : list (list Z)) (source lower upper stock : Z) : Prop :=
  0 <= stock /\
  stock < Zlength (Znth source table []) /\
  Znth stock (Znth source table []) 0 <> STOCK_NEG_INF /\
  lower <= stock <= upper.

Definition StockSellCandidate
    (bid sell : list Z) (table : list (list Z))
    (max_stock day source stock amount value : Z) : Prop :=
  (amount = 0 /\
   value = Znth stock (Znth (day - 1) table []) 0) \/
  (1 <= amount <= Znth (day - 1) sell 0 /\
   stock + amount <= max_stock /\
   Znth (stock + amount) (Znth source table []) 0 <> STOCK_NEG_INF /\
   value =
     Znth (stock + amount) (Znth source table []) 0 +
     amount * Znth (day - 1) bid 0).
End Legacy.

Module Modern.
Import Legacy.
Include PVbench.Algorithms.stock_trading.rocq.spec_lib.Modern.
(* Monomorphic spelling needed when passing Zlength through C extern map. *)
Definition StockRowLength : list Z -> Z := @Zlength Z.

Definition StockPortfolioValue (ask bid buy sell : list Z)
    (max_stock wait horizon stock value : Z) : Prop :=
  0 <= stock <= max_stock /\
  ((value = STOCK_NEG_INF /\ ~ exists profit,
      StockFeasiblePortfolio ask bid buy sell max_stock wait horizon stock profit) \/
   max_value_of_subset Z.le
      (fun profit => StockFeasiblePortfolio ask bid buy sell max_stock wait horizon stock profit)
      (fun profit : Z => profit) value).

Definition StockSellCellValue (bid sell : list Z) (table : list (list Z))
    (max_stock day source stock value : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : Z * Z => Legacy.StockSellCandidate bid sell table max_stock day source stock
       (fst candidate) (snd candidate)) (@snd Z Z) value.

Definition StockBuyCandidate
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock day source stock amount value : Z) : Prop :=
  (amount = 0 /\
   StockSellCellValue bid sell table max_stock day source stock value) \/
  (1 <= amount <= Znth (day - 1) buy 0 /\
   amount <= stock /\
   Znth (stock - amount) (Znth source table []) 0 <> STOCK_NEG_INF /\
   value =
     Znth (stock - amount) (Znth source table []) 0 -
     amount * Znth (day - 1) ask 0).

Definition StockBuyCellValue (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock day source stock value : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : Z * Z => StockBuyCandidate ask bid buy sell table max_stock day source stock
       (fst candidate) (snd candidate)) (@snd Z Z) value /\
  exists zero_value, StockSellCellValue bid sell table max_stock day source stock zero_value.

Definition StockFillRows (table : list (list Z)) (days max_stock row : Z) : Prop :=
  forall d stock, 0 <= d < row -> 0 <= stock < max_stock + 1 ->
    Znth stock (Znth d table []) 0 = StockInitialCell d stock.

Definition StockFillCells (current_row : list Z) (max_stock row col : Z) : Prop :=
  forall stock, 0 <= stock < col ->
    Znth stock current_row 0 = StockInitialCell row stock.

Definition StockDaysDone (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait next_day : Z) : Prop :=
  forall day stock, 0 <= day < next_day -> 0 <= stock <= max_stock ->
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (Znth stock (Znth day table []) 0).

Definition StockCopyProgress (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day col : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  Forall2 eq (sublist 0 col (Znth day table []))
    (sublist 0 col (Znth (day - 1) table [])).

Definition StockEarlyBuyProgress (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day next_stock : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  Znth 0 (Znth day table []) 0 = Znth 0 (Znth (day - 1) table []) 0 /\
  forall stock, 1 <= stock <= max_stock ->
    if Z_lt_dec stock next_stock then
      Znth stock (Znth day table []) 0 =
      Z.max (Znth stock (Znth (day - 1) table []) 0) (-stock * Znth (day - 1) ask 0)
    else Znth stock (Znth day table []) 0 = Znth stock (Znth (day - 1) table []) 0.

Definition StockSellQueue
    (table : list (list Z)) (queue : list Z)
    (source price lower upper head tail : Z) : Prop :=
  Forall (StockFiniteIndexInWindow table source lower upper) (sublist head tail queue) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 > Znth right queue 0 /\
     StockSellScore table source price (Znth left queue 0) >
     StockSellScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source lower upper candidate ->
     exists pos, head <= pos < tail /\
       Znth pos queue 0 <= candidate /\
       StockSellScore table source price candidate <=
       StockSellScore table source price (Znth pos queue 0)).

Definition StockSellQueueExpiring
    (table : list (list Z)) (queue : list Z)
    (source price lower current_upper head tail : Z) : Prop :=
  StockSellQueue table queue source price
    lower (current_upper + 1) head tail \/
  StockSellQueue table queue source price
    lower current_upper head tail.

Definition StockSellQueuePopping
    (table : list (list Z)) (queue : list Z)
    (source price incoming upper head tail : Z) : Prop :=
  StockFiniteTableIndex table source incoming /\
  Forall (StockFiniteIndexInWindow table source (incoming + 1) upper) (sublist head tail queue) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 > Znth right queue 0 /\
     StockSellScore table source price (Znth left queue 0) >
     StockSellScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source incoming upper candidate ->
     StockSellScore table source price candidate <=
       StockSellScore table source price incoming \/
     exists pos, head <= pos < tail /\
       Znth pos queue 0 <= candidate /\
       StockSellScore table source price candidate <=
       StockSellScore table source price (Znth pos queue 0)).

Definition StockBuyQueue
    (table : list (list Z)) (queue : list Z)
    (source price lower upper head tail : Z) : Prop :=
  Forall (StockFiniteIndexInWindow table source lower upper) (sublist head tail queue) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 < Znth right queue 0 /\
     StockBuyScore table source price (Znth left queue 0) >
     StockBuyScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source lower upper candidate ->
     exists pos, head <= pos < tail /\
       candidate <= Znth pos queue 0 /\
       StockBuyScore table source price candidate <=
       StockBuyScore table source price (Znth pos queue 0)).

Definition StockBuyQueueExpiring
    (table : list (list Z)) (queue : list Z)
    (source price current_lower upper head tail : Z) : Prop :=
  StockBuyQueue table queue source price
    (current_lower - 1) upper head tail \/
  StockBuyQueue table queue source price
    current_lower upper head tail.

Definition StockBuyQueuePopping
    (table : list (list Z)) (queue : list Z)
    (source price lower incoming head tail : Z) : Prop :=
  StockFiniteTableIndex table source incoming /\
  Forall (StockFiniteIndexInWindow table source lower (incoming - 1)) (sublist head tail queue) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 < Znth right queue 0 /\
     StockBuyScore table source price (Znth left queue 0) >
     StockBuyScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source lower incoming candidate ->
     StockBuyScore table source price candidate <=
       StockBuyScore table source price incoming \/
     exists pos, head <= pos < tail /\
       candidate <= Znth pos queue 0 /\
       StockBuyScore table source price candidate <=
       StockBuyScore table source price (Znth pos queue 0)).

Definition StockSellProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day source next_stock : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  Forall2 eq (sublist 0 (next_stock + 1) (Znth day table []))
    (sublist 0 (next_stock + 1) (Znth (day - 1) table [])) /\
  (forall stock,
     next_stock < stock < max_stock ->
     StockSellCellValue bid sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)) /\
  Znth max_stock (Znth day table []) 0 =
    Znth max_stock (Znth (day - 1) table []) 0.

Definition StockBuyProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day source next_stock : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  (forall stock,
     0 <= stock < next_stock ->
     StockBuyCellValue ask bid buy sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)) /\
  (forall stock,
     next_stock <= stock <= max_stock ->
     StockSellCellValue bid sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)).

Definition StockAnswerProgress (ask bid buy sell : list Z) (table : list (list Z))
    (days max_stock wait next_stock answer : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait (days + 1) /\
  ((next_stock = 0 /\ answer = 0) \/
   max_value_of_subset Z.le
     (fun candidate : Z * Z => 0 <= fst candidate < next_stock /\
       StockFeasiblePortfolio ask bid buy sell max_stock wait days
          (fst candidate) (snd candidate)) (@snd Z Z) answer).
End Modern.

Export Legacy Modern.
