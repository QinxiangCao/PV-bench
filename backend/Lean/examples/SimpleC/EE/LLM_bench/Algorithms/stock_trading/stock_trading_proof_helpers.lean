import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.StockProofInternal
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2

theorem merge_cell (p n m r c v : Int) (rows : List (List Int)) (d : List Int)
    (hr : 0 ≤ r ∧ r < n) (hc : 0 ≤ c ∧ c < m) :
    (((p+(r*m+c)*sizeof(INT)) # Int |-> v) **
     intArray.missing_i (p+r*m*sizeof(INT)) c 0 m (Znth r rows d) **
     SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i p r 0 n m rows |--
     SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full p n m (replace_Znth r (replace_Znth c v (Znth r rows d)) rows)) := by
  have haddr : p+r*m*sizeof(INT)+c*sizeof(INT) = p+(r*m+c)*sizeof(INT) := by
    simp only [Int.add_mul]; omega
  rw [← haddr]
  have hrow : (((p+r*m*sizeof(INT)+c*sizeof(INT)) # Int |-> v) **
      intArray.missing_i (p+r*m*sizeof(INT)) c 0 m (Znth r rows d) |--
      intArray.full (p+r*m*sizeof(INT)) m (replace_Znth c v (Znth r rows d))) :=
    intArray.missing_i_merge_to_full (p+r*m*sizeof(INT)) c m v (Znth r rows d) hc
  sep_apply hrow
  have htable : (intArray.full (p+r*m*sizeof(INT)) m (replace_Znth c v (Znth r rows d)) **
      SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i p r 0 n m rows |--
      SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full p n m (replace_Znth r (replace_Znth c v (Znth r rows d)) rows)) :=
    intArray2.missing_i_merge_to_full p r n m rows (replace_Znth c v (Znth r rows d)) hr
  sep_apply htable
  cancel

theorem restore_cell (p n m r c : Int) (rows : List (List Int)) (d : List Int)
    (hr : 0 ≤ r ∧ r < n) (hc : 0 ≤ c ∧ c < m) :
    (((p+(r*m+c)*sizeof(INT)) # Int |-> Znth c (Znth r rows d) 0) **
     intArray.missing_i (p+r*m*sizeof(INT)) c 0 m (Znth r rows d) **
     SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i p r 0 n m rows |-- SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full p n m rows) := by
  sep_apply (merge_cell p n m r c (Znth c (Znth r rows d) 0) rows d hr hc)
  simp only [replace_Znth_Znth]
  cancel

open stock_trading_lib
private theorem table_shape_replace (table : List (List Int)) (days max_stock row : Int)
    (newrow : List Int) (hs : StockTableShape table days max_stock)
    (hr : 0 ≤ row ∧ row < days+1) (hl : Zlength newrow = max_stock+1) :
    StockTableShape (replace_Znth row newrow table) days max_stock := by
  refine ⟨?_,?_⟩
  · rw [Zlength_replace_Znth]; exact hs.1
  · intro r h
    by_cases he : r = row
    · subst r; rw [Znth_replace_Znth_Same [] table row newrow (by rw [hs.1]; exact hr)]; exact hl
    · rw [Znth_replace_Znth_Diff [] table row r newrow (by rw [hs.1]; exact hr) (by rw [hs.1]; exact h) (Ne.symm he)]
      exact hs.2 r h

private theorem table_bounded_replace (table : List (List Int)) (days max_stock row : Int)
    (newrow : List Int) (hs : StockTableShape table days max_stock)
    (hb : StockTableValuesBounded table days max_stock)
    (hr : 0 ≤ row ∧ row < days+1)
    (hn : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock newrow 0 ∧ Znth stock newrow 0 ≤ STOCK_MAX_PROFIT) :
    StockTableValuesBounded (replace_Znth row newrow table) days max_stock := by
  intro r stock h hk
  by_cases he : r = row
  · subst r; rw [Znth_replace_Znth_Same [] table row newrow (by rw [hs.1]; exact hr)]; exact hn stock hk
  · rw [Znth_replace_Znth_Diff [] table row r newrow (by rw [hs.1]; exact hr) (by rw [hs.1]; exact h) (Ne.symm he)]
    exact hb r stock h hk

private theorem row_bounded_replace (row : List Int) (max_stock col value : Int)
    (hl : Zlength row = max_stock+1)
    (hc : 0 ≤ col ∧ col < max_stock+1)
    (hv : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT)
    (hb : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock row 0 ∧ Znth stock row 0 ≤ STOCK_MAX_PROFIT) :
    ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock (replace_Znth col value row) 0 ∧ Znth stock (replace_Znth col value row) 0 ≤ STOCK_MAX_PROFIT := by
  intro stock hs
  by_cases he : stock = col
  · subst stock; rw [Znth_replace_Znth_Same 0 row col value (by omega)]; exact hv
  · rw [Znth_replace_Znth_Diff 0 row col stock value (by omega) (by omega) (Ne.symm he)]
    exact hb stock hs

private theorem days_done_replace (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait next_day row : Int) (newrow : List Int)
    (hd : StockDaysDone ask bid buy sell table max_stock wait next_day)
    (hr : 0 ≤ row ∧ row < Zlength ask+1) (hnr : next_day ≤ row)
    (hl : Zlength newrow = max_stock+1)
    (hb : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock newrow 0 ∧ Znth stock newrow 0 ≤ STOCK_MAX_PROFIT) :
    StockDaysDone ask bid buy sell (replace_Znth row newrow table) max_stock wait next_day := by
  refine ⟨table_shape_replace table (Zlength ask) max_stock row newrow hd.1 hr hl,
    table_bounded_replace table (Zlength ask) max_stock row newrow hd.1 hd.2.1 hr hb,hd.2.2.1,?_⟩
  intro day stock hday hs
  rw [Znth_replace_Znth_Diff [] table row day newrow (by rw [hd.1.1]; exact hr) (by rw [hd.1.1]; omega) (by omega)]
  exact hd.2.2.2 day stock hday hs

theorem sell_cell_queue (ask bid buy sell : List Int) (table : List (List Int))
    (days max_stock wait day source stock : Int) (queue : List Int)
    (price cap head tail best value : Int)
    (hi : StockInputsBounded ask bid buy sell days max_stock)
    (hp : StockSellProgress ask bid buy sell table max_stock wait day source stock)
    (hstock : 0 ≤ stock ∧ stock < max_stock)
    (hq : StockSellQueue table queue source price (stock+1) (stock+cap) head tail)
    (hht : head < tail) (hbest : best = Znth head queue 0)
    (hprice : price = Znth (day-1) bid 0) (hcap : cap = Znth (day-1) sell 0)
    (hv : value = StockSellScore table source price best - stock*price) :
    StockSellCellValue bid sell table max_stock day source stock
      (max (Znth stock (Znth day table []) 0) value) := by
  have hcopy := hp.2.2.2.2.2.1 stock (by omega)
  have hday := hp.2.1
  have hsrc := hp.2.2.2.1
  have hrow := hp.1.1.2 source (by omega)
  have hentry := hq.2.1 head (by omega)
  rw [← hbest] at hentry
  rcases hentry with ⟨hb0,hbl,hbf,hbr⟩
  have hcandidate : StockSellCandidate bid sell table max_stock day source stock (best-stock) value := by
    right
    refine ⟨by omega,by omega,?_,?_⟩
    · simpa only [show stock+(best-stock)=best by omega] using hbf
    · rw [show stock+(best-stock)=best by omega, ← hprice]
      simp only [Int.sub_mul]
      unfold StockSellScore at hv
      omega
  refine ⟨?_,?_⟩
  · by_cases he : Znth stock (Znth day table []) 0 ≤ value
    · rw [Int.max_eq_right he]; exact ⟨best-stock,hcandidate⟩
    · rw [Int.max_eq_left (by omega)]
      exact ⟨0,Or.inl ⟨rfl,hcopy⟩⟩
  · intro amount candidate hc
    rcases hc with ⟨ha,hc⟩ | ⟨ha,hb,hn,hc⟩
    · have hm := Int.le_max_left (Znth stock (Znth day table []) 0) value
      omega
    · obtain ⟨pos,hpos,hindex,hscore⟩ := hq.2.2.2 (stock+amount) ⟨by omega,by omega,hn,by omega⟩
      have hhead : StockSellScore table source price (Znth pos queue 0) ≤ StockSellScore table source price best := by
        by_cases he : pos = head
        · subst pos; rw [hbest] <;> omega
        · have hh := (hq.2.2.1 head pos (by omega)).2
          rw [← hbest] at hh
          omega
      have hm := Int.le_max_right (Znth stock (Znth day table []) 0) value
      unfold StockSellScore at hhead hscore hv
      rw [← hprice] at hc
      simp only [Int.add_mul] at hscore
      omega

theorem sell_replace_step (ask bid buy sell : List Int) (table : List (List Int))
    (days max_stock wait day source stock value : Int)
    (hi : StockInputsBounded ask bid buy sell days max_stock) (hw : 0 ≤ wait)
    (hp : StockSellProgress ask bid buy sell table max_stock wait day source stock)
    (hs : 0 ≤ stock ∧ stock < max_stock)
    (hc : StockSellCellValue bid sell table max_stock day source stock value) :
    let row := replace_Znth stock value (Znth day table [])
    let table' := replace_Znth day row table
    StockSellProgress ask bid buy sell table' max_stock wait day source (stock-1) ∧
    StockTableShape table' days max_stock := by
  have hday := hp.2.1
  have hsource := hp.2.2.1
  have hsr := hp.2.2.2.1
  have hdaydays : day ≤ days := by rw [← hi.1]; omega
  have hsound := StockSellCellValue_sound__buy_semantics ask bid buy sell table days max_stock wait day source stock value hi hw hday.1 hdaydays hsource hsr (by omega) hp.1 hc
  have hv : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT := by
    rcases hsound with he | hf
    · unfold STOCK_NEG_INF STOCK_MAX_PROFIT at *; omega
    · have hr := StockFeasiblePortfolio_profit_range__buy_semantics ask bid buy sell days max_stock wait day stock value hi hw hdaydays hf
      omega
  have hshape := hp.1.1
  have hlen := hshape.1
  have hrow := hshape.2 day (by omega)
  have hnewlen : Zlength (replace_Znth stock value (Znth day table [])) = max_stock+1 := by
    rw [Zlength_replace_Znth]; exact hrow
  have hbound := row_bounded_replace (Znth day table []) max_stock stock value hrow (by omega) hv (hp.1.2.1 day · (by omega))
  have hdone := days_done_replace ask bid buy sell table max_stock wait day day _ hp.1 (by omega) (by omega) hnewlen hbound
  have hprev := Znth_replace_Znth_Diff ([] : List Int) table day (day-1) (replace_Znth stock value (Znth day table [])) (by omega) (by omega) (by omega)
  have hcur := Znth_replace_Znth_Same ([] : List Int) table day (replace_Znth stock value (Znth day table [])) (by omega)
  have hshapeDays : StockTableShape table days max_stock := by rw [← hi.1]; exact hshape
  have hport (k v : Int) (hc' : StockSellCellValue bid sell table max_stock day source k v) :=
    StockSellCellValue_replace_current_row__buy_semantics bid sell table max_stock day source k v stock value days hshapeDays (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hc'
  dsimp only
  refine ⟨⟨hdone,hday,hsource,hsr,by omega,?_,?_,?_⟩,?_⟩
  · intro k hk
    rw [hcur,Znth_replace_Znth_Diff 0 (Znth day table []) stock k value (by omega) (by omega) (by omega),hprev]
    exact hp.2.2.2.2.2.1 k (by omega)
  · intro k hk
    by_cases he : k = stock
    · subst k
      rw [hcur,Znth_replace_Znth_Same 0 (Znth day table []) stock value (by omega)]
      exact hport stock value hc
    · rw [hcur,Znth_replace_Znth_Diff 0 (Znth day table []) stock k value (by omega) (by omega) (by omega)]
      exact hport k _ (hp.2.2.2.2.2.2.1 k (by omega))
  · rw [hcur,Znth_replace_Znth_Diff 0 (Znth day table []) stock max_stock value (by omega) (by omega) (by omega),hprev]
    exact hp.2.2.2.2.2.2.2
  · rw [← hi.1]; exact hdone.1

theorem sell_queue_replace (table : List (List Int)) (queue : List Int)
    (source price lower upper head tail row : Int) (v : List Int)
    (hs : 0 ≤ source ∧ source < Zlength table) (hr : 0 ≤ row ∧ row < Zlength table)
    (hne : source ≠ row) (hq : StockSellQueue table queue source price lower upper head tail) :
    StockSellQueue (replace_Znth row v table) queue source price lower upper head tail := by
  unfold StockSellQueue StockFiniteIndexInWindow StockSellScore at *
  simpa only [Znth_replace_Znth_Diff ([] : List Int) table row source v hr hs (Ne.symm hne)] using hq

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.StockProofInternal
