Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import PVbench.Codeforces.examples_shard01.P090_1027G_x_mouse_in_the_campus.rocq.spec_lib.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint coprime_count (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      coprime_count n k +
      if Z.eqb (Z.gcd (Z.of_nat (S k)) n) 1 then 1 else 0
  end.

Definition EulerPhi (n : Z) : Z := coprime_count n (Z.to_nat n).

Fixpoint order_search (x n k : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 1
  | S fuel' =>
      if Z.eqb (Z.pow x k mod n) 1
      then k
      else order_search x n (k + 1) fuel'
  end.

Definition Ord (x n : Z) : Z :=
  if Z.eqb n 1 then 1
  else order_search (x mod n) n 1 (Z.to_nat (EulerPhi n)).

Definition IsPrime (p : Z) : Prop :=
  1 < p /\
  forall q, 1 < q < p -> p mod q <> 0.

Definition CycleTerm (x d : Z) : Z :=
  if Z.eqb d 1 then 0 else EulerPhi d / Ord (x mod d) d.

Fixpoint sum_nat_range (first count : nat) (f : nat -> Z) : Z :=
  match count with
  | O => 0
  | S count' => f first + sum_nat_range (S first) count' f
  end.

Fixpoint walk_suffix_lists (pr pe : list Z) (x d : Z) : Z :=
  match pr, pe with
  | p :: pr', exponent :: pe' =>
      sum_nat_range 0 (S (Z.to_nat exponent))
        (fun e => walk_suffix_lists pr' pe' x (d * Z.pow p (Z.of_nat e)))
  | _, _ => CycleTerm x d
  end.

Definition WalkSuffix (pr pe : list Z) (x i d : Z) : Z :=
  walk_suffix_lists (skipn (Z.to_nat i) pr) (skipn (Z.to_nat i) pe) x d.

Definition WalkExpSuffix
    (pr pe : list Z) (x i next_e d : Z) : Z :=
  let exponent := Znth i pe 0 in
  sum_nat_range (Z.to_nat next_e)
    (Z.to_nat (exponent - next_e + 1))
    (fun e =>
       WalkSuffix pr pe x (i + 1)
         (d * Z.pow (Znth i pr 0) (Z.of_nat e))).

Definition WalkLoopState
    (pr pe : list Z) (x i d before current next_e : Z) : Prop :=
  current + WalkExpSuffix pr pe x i next_e d =
  before + WalkSuffix pr pe x i d.

Definition WalkGlobalBounds (m x : Z) : Prop :=
  2 <= m <= 100000000000000 /\
  1 <= x < m /\
  Z.gcd x m = 1.

Definition WalkMachineBounds (m d phi ord : Z) : Prop :=
  0 < d <= m /\ 0 < phi <= m /\ 0 < ord <= m.

Definition WalkBudget (m before work : Z) : Prop :=
  0 <= before /\ 0 <= work /\ before + work <= m.

Definition WalkPendingState
    (pr pe : list Z) (m x i d before current next_e : Z) : Prop :=
  WalkLoopState pr pe x i d before current next_e /\
  WalkBudget m current (WalkExpSuffix pr pe x i next_e d).

Definition WalkExponentState
    (m p exponent max_exponent pk ph : Z) : Prop :=
  2 <= p <= m /\
  1 <= exponent <= max_exponent + 1 /\
  1 <= pk <= m /\ 1 <= ph <= m /\
  pk = Z.pow p (exponent - 1) /\
  ph = EulerPhi pk.

Definition MulLoopState (a0 b0 modulus a b r : Z) : Prop :=
  (r + a * b) mod modulus = (a0 * b0) mod modulus.

Definition PowLoopState (base exponent modulus b e r : Z) : Prop :=
  (r * Z.pow b e) mod modulus = Z.pow base exponent mod modulus.

Definition GcdLoopState (a0 b0 a b : Z) : Prop :=
  Z.gcd a b = Z.gcd a0 b0.

Definition OrderInput (x modulus phi : Z) : Prop :=
  1 < modulus /\
  phi = EulerPhi modulus /\
  Z.gcd x modulus = 1 /\
  0 < phi <= modulus /\
  0 < Ord x modulus /\
  (Ord x modulus | phi) /\
  Z.pow x phi mod modulus = 1.

Definition OrderResult (x modulus result : Z) : Prop :=
  result = Ord x modulus /\
  0 < result /\
  (result | EulerPhi modulus) /\
  Z.pow x result mod modulus = 1.

Definition OrderTrialState
    (x modulus phi q t ord : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < t /\ t <= phi /\ (t | phi) /\
  0 < ord /\ ord <= phi /\ (ord | phi) /\
  (Ord x modulus | ord) /\
  Z.pow x ord mod modulus = 1 /\
  forall prime, IsPrime prime -> prime < q -> t mod prime <> 0.

Definition OrderFactorState
    (x modulus phi q t ord : Z) : Prop :=
  OrderTrialState x modulus phi q t ord /\ IsPrime q.

Definition OrderStripState
    (x modulus phi q t ord : Z) : Prop :=
  OrderFactorState x modulus phi q t ord /\ t mod q <> 0.

Fixpoint factor_product (pr pe : list Z) : Z :=
  match pr, pe with
  | p :: pr', e :: pe' => Z.pow p e * factor_product pr' pe'
  | _, _ => 1
  end.

Definition FactorPrefix
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  Zlength pr = Zlength pe /\
  0 <= Zlength pr <= 64 /\
  2 <= candidate /\
  0 < remainder <= m /\
  m = factor_product pr pe * remainder /\
  (forall k, 0 <= k < Zlength pr ->
     IsPrime (Znth k pr 0) /\
     1 <= Znth k pe 0 /\
     Znth k pr 0 < candidate) /\
  (forall prime, IsPrime prime -> prime < candidate ->
     remainder mod prime <> 0).

Definition TrialState
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  FactorPrefix m candidate remainder pr pe.

Definition FactorAtPrime
    (m candidate original_remainder remainder exponent : Z)
    (pr pe : list Z) : Prop :=
  FactorPrefix m candidate original_remainder pr pe /\
  IsPrime candidate /\
  original_remainder mod candidate = 0 /\
  0 <= exponent /\
  original_remainder = Z.pow candidate exponent * remainder /\
  0 < remainder <= original_remainder.

Definition ValidFactorTable (m : Z) (pr pe : list Z) : Prop :=
  Zlength pr = Zlength pe /\
  0 <= Zlength pr <= 64 /\
  m = factor_product pr pe /\
  (forall k, 0 <= k < Zlength pr ->
     IsPrime (Znth k pr 0) /\ 1 <= Znth k pe 0) /\
  (forall j k,
     0 <= j /\ j < k /\ k < Zlength pr ->
     Znth j pr 0 < Znth k pr 0).

Inductive PrefixSelected (pr pe : list Z) : Z -> Z -> Prop :=
| prefix_selected_zero :
    PrefixSelected pr pe 0 1
| prefix_selected_step : forall i d e,
    PrefixSelected pr pe i d ->
    0 <= i < Zlength pr ->
    0 <= e <= Znth i pe 0 ->
    PrefixSelected pr pe (i + 1)
      (d * Z.pow (Znth i pr 0) e).

Definition PrefixChoice
    (pr pe : list Z) (x i d phi ord : Z) : Prop :=
  Zlength pr = Zlength pe /\
  0 <= i <= Zlength pr /\
  PrefixSelected pr pe i d /\
  0 < d /\ 0 < phi /\ 0 < ord /\
  phi = EulerPhi d /\ ord = Ord x d /\ Z.gcd x d = 1.

Definition PrimePowerTransition
    (x d phi ord p e pk ph o g next_d next_phi next_ord : Z) : Prop :=
  0 < d /\ 1 < p /\ 1 <= e /\
  pk = Z.pow p e /\
  ph = EulerPhi pk /\
  o = Ord (x mod pk) pk /\
  g = Z.gcd ord o /\
  next_d = d * pk /\
  next_phi = phi * ph /\
  next_ord = ord / g * o /\
  Z.gcd d pk = 1 /\
  EulerPhi next_d = EulerPhi d * EulerPhi pk /\
  Ord x next_d = next_ord /\
  0 < next_d /\ 0 < next_phi /\ 0 < next_ord.

Definition CycleAnswer (m x total : Z) : Prop :=
  0 <= total <= m /\ Spec m x (total + 1).

Definition DivisorCycleSum (m x total : Z) : Prop :=
  min_value_of_subset Z.le
    (fun v => exists traps, CatchesAll m x traps /\ v = Zlength traps)
    (fun z => z) (total + 1).

(** Projection/transition interface.  The difficult facts remain explicit
    premises; these lemmas never manufacture number theory. *)

(** Consumer-designed order states.  These are deliberately parallel to the
    earlier trial/factor/strip predicates: the original declarations remain
    available, while the C order loop uses this strengthened family.  The
    ghost [excess] satisfies [ord = Ord * excess], and prime support records
    that every still-removable excess prime is present in the unprocessed
    remainder (apart from the one active prime during stripping). *)

Definition OrderCore
    (x modulus phi ord excess : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < ord /\ ord <= phi /\ (ord | phi) /\
  0 < excess /\
  ord = Ord x modulus * excess /\
  Z.pow x ord mod modulus = 1.

Definition PrimeSupport (excess remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> (p | remainder).

Definition PrimeSupportExcept (excess active remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> p = active \/ (p | remainder).

Definition NoPrimeBelow (candidate remainder : Z) : Prop :=
  forall p, IsPrime p -> p < candidate -> remainder mod p <> 0.

Definition OrderTrialStateEx
    (x modulus phi candidate remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow candidate remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupport excess remainder.

Definition OrderFactorStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow active remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupportExcept excess active remainder.

Definition OrderStripStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderFactorStateEx x modulus phi active remainder ord /\
  remainder mod active <> 0.

Definition OrderFinalStateEx
    (x modulus phi active ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    (forall p, IsPrime p -> (p | excess) -> p = active).

Definition OrderPowerLaw (x modulus : Z) : Prop :=
  forall k, 0 <= k ->
    (Z.pow x k mod modulus = 1 <-> (Ord x modulus | k)).

(** VC-facing wrappers for the exact C guards and quotient assignments. *)

(** Consumer-driven number-theory and transition closure, transplanted from
    the independently kernel-checked lemma_staging graph.  Each source is kept
    in its original module boundary and exported for generated VC consumers. *)

Module P090_OrderExcess.

Local Open Scope Z_scope.

Module P090_OrderExcess.

(** The definitions in this module are deliberately namespaced staging
    replacements.  [excess] is the mathematical quotient [ord / Ord], but the
    invariant records it by multiplication so no division side condition is
    hidden in a state predicate. *)

Definition OrderCore
    (x modulus phi ord excess : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < ord /\ ord <= phi /\ (ord | phi) /\
  0 < excess /\
  ord = Ord x modulus * excess /\
  Z.pow x ord mod modulus = 1.

Definition PrimeSupport (excess remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> (p | remainder).

Definition PrimeSupportExcept (excess active remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> p = active \/ (p | remainder).

Definition NoPrimeBelow (candidate remainder : Z) : Prop :=
  forall p, IsPrime p -> p < candidate -> remainder mod p <> 0.

Definition OrderTrialStateEx
    (x modulus phi candidate remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow candidate remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupport excess remainder.

Definition OrderFactorStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow active remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupportExcept excess active remainder.

Definition OrderStripStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderFactorStateEx x modulus phi active remainder ord /\
  remainder mod active <> 0.

Definition OrderFinalStateEx
    (x modulus phi active ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    (forall p, IsPrime p -> (p | excess) -> p = active).

(** Explicit interfaces for the foundational number theory that is not proved
    by this staging file.  They are never fields of the program-state
    predicates: every lemma that needs one takes it as a visible hypothesis. *)

Definition OrderPowerLaw (x modulus : Z) : Prop :=
  forall k, 0 <= k ->
    (Z.pow x k mod modulus = 1 <-> (Ord x modulus | k)).

Definition PrimeFactorExistsLaw : Prop :=
  forall n, 1 < n -> exists p, IsPrime p /\ (p | n).

Definition PrimeDivisorProductLaw : Prop :=
  forall p a b, IsPrime p -> (p | a * b) -> (p | a) \/ (p | b).

Definition PrimeDivisorOfPrimeLaw : Prop :=
  forall p q, IsPrime p -> IsPrime q -> (p | q) -> p = q.

Definition SmallestRemainingDivisorPrimeLaw : Prop :=
  forall candidate remainder,
    2 <= candidate ->
    0 < remainder ->
    NoPrimeBelow candidate remainder ->
    remainder mod candidate = 0 ->
    IsPrime candidate.

Definition ResidualRemainderPrimeLaw : Prop :=
  forall candidate remainder,
    2 <= candidate ->
    1 < remainder ->
    candidate * candidate > remainder ->
    NoPrimeBelow candidate remainder ->
    IsPrime remainder.

End P090_OrderExcess.
End P090_OrderExcess.
Import P090_OrderExcess.

Module P090_OrderFoundations.

Local Open Scope Z_scope.

Import P090_OrderExcess.P090_OrderExcess.

Module P090_OrderFoundations.

(** The unqualified [OrderPowerLaw] is false: it has no coprimality
    hypothesis.  The concrete failure below uses exponent one. *)

(** The case-local primality predicate is extensionally the standard Rocq
    integer primality predicate. *)

End P090_OrderFoundations.
End P090_OrderFoundations.
Import P090_OrderFoundations.

Module P090_OrderExact.

Local Open Scope Z_scope.

Import P090_OrderExcess.P090_OrderExcess.

Module P090_OrderExact.

End P090_OrderExact.
End P090_OrderExact.
Import P090_OrderExact.

Module P090_FactorTable.

Import ListNotations.
Local Open Scope Z_scope.

(** The on-disk [FactorPrefix] records that every stored prime is below the
    current candidate, but it does not record the relative order of the stored
    entries.  This additional conjunct is the missing construction history
    needed by [ValidFactorTable]. *)
Definition StrictPrimePrefix (pr : list Z) : Prop :=
  forall j k,
    0 <= j /\ j < k /\ k < Zlength pr ->
    Znth j pr 0 < Znth k pr 0.

Definition StrictFactorPrefix
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  FactorPrefix m candidate remainder pr pe /\ StrictPrimePrefix pr.

(** A completed division by the current prime may be appended.  All premises
    are primitive facts produced by the factor loop: exact division history,
    positive exponent/remainder, the failed next divisibility test, and one
    free table slot. *)
(** If the trial loop exits with a prime residual, the prefix exclusion fact
    itself proves that the residual cannot be smaller than the candidate. *)
End P090_FactorTable.
Import P090_FactorTable.

Module P090_FactorFoundations.

Import ListNotations.
Local Open Scope Z_scope.

(** A list-level form of the facts supplied by [FactorPrefix]. *)
Definition FactorEntriesAtLeastTwo (pr pe : list Z) : Prop :=
  forall k, 0 <= k < Zlength pr ->
    2 <= Znth k pr 0 /\ 1 <= Znth k pe 0.

(** Bridge between Coq's standard primality and the case's trial-division
    definition. *)
(** The complete factor-loop exit: either no residual remains, or the square
    guard makes the residual prime and it is appended into a provably free
    slot. *)
End P090_FactorFoundations.
Import P090_FactorFoundations.

Module P090_WalkFoundations.

Import ListNotations.
Local Open Scope Z_scope.

Module ETI := euler_theorem_inverse_lib.

(** The case's tail-recursive count is exactly the already-verified canonical
    finite residue count used by the Euler-theorem development. *)

(** Strict positivity needs a positive modulus.  The concrete zero case is a
    compiled counterexample to any unconditional positivity claim. *)

(** The arithmetic and CRT portions of the order transition. *)

Definition ExactOrderCriterion (x modulus candidate : Z) : Prop :=
  0 < candidate /\
  forall exponent,
    0 <= exponent ->
    ((x ^ exponent) mod modulus = 1 <-> (candidate | exponent)).

(** [Ord] is only a genuine multiplicative order under coprimality and an
    Euler bound.  Its fallback value is observably not an order otherwise. *)

(** Nonnegativity and the exact structural decomposition of the walk. *)

(** Multiplication by a unit preserves every gcd stratum.  This is the first
    orbit fact needed by the final catching-set argument. *)

(** Unresolved foundations, deliberately not represented by assumptions:

    - prove that the bounded [order_search] defining [Ord] satisfies
      [ExactOrderCriterion] when the base is coprime to a positive modulus;
    - prove that [ValidFactorTable] and [PrefixSelected] enumerate every
      positive divisor exactly once (unique prime factorization is the missing
      ingredient connecting the list representation to divisibility);
    - use that bijection to identify [WalkSuffix pr pe x 0 1] with the sum of
      [EulerPhi d / Ord (x mod d) d] over non-unit divisors [d] of [m];
    - prove the divisor identity [sum_(d|m) EulerPhi d = m], yielding the
      cumulative walk budget after order positivity and divisibility;
    - strengthen [gcd_stratum_preserved] to the orbit theorem: each nonzero
      gcd stratum is isomorphic to the units modulo its associated divisor,
      multiplication by [x] has orbit length [Ord], and any catching set must
      meet every such orbit.  That supplies both the catching-set construction
      and its matching lower bound.

    The two counterexamples above explain why positivity needs [n >= 1] and
    why the exact-order theorem must retain the coprimality/Euler hypotheses. *)
End P090_WalkFoundations.
Import P090_WalkFoundations.

Module P090_OrbitOptimality.

Import ListNotations.
Local Open Scope Z_scope.

(** Generic finite-sum infrastructure used by the divisor budget. *)

(** The complete divisor-totient identity for a prime power.  This is the
    atomic case of [sum_(d|m) phi(d) = m], proved against the case's actual
    [EulerPhi] definition via the verified bridge in [P090_WalkFoundations]. *)

(** For a one-prime factor table, the walk's cumulative work is bounded by
    the exact prime-power divisor-totient sum.  No statement about [Spec] or
    orbit optimality is used. *)

(** Modular cancellation by a unit gives the exact return-time theorem for a
    unit orbit.  This is the core lower-bound fact: a unit orbit cannot return
    before its exact multiplicative order. *)

(** A catching set really intersects the forward orbit of every unit start;
    combined with [unit_orbit_no_early_return], distinct orbit classes require
    distinct traps.  Constructing and counting a complete representative list
    remains the finite-quotient step documented below. *)

(** Exact unresolved boundary.

    The prime-power identity and budget above are complete.  Extending them to
    arbitrary [ValidFactorTable] requires the still-unproved conversion from
    its [Znth]-based sortedness clauses to an inductive pairwise-coprime table;
    the mathematical induction then multiplies the prime-power sums using
    [euler_phi_coprime_multiplicative].

    The orbit-return theorem is also complete, but the current library has no
    finite quotient construction for the equivalence relation generated by
    unit multiplication.  A full [Spec] theorem still needs, without choice
    axioms: (1) a concrete list containing exactly one representative of each
    unit orbit; (2) its length [EulerPhi d / Ord (x mod d) d]; (3) transport
    between the gcd-[m/d] stratum modulo [m] and units modulo [d]; and (4) the
    disjoint-orbit pigeonhole argument showing every [CatchesAll] list has at
    least one member per representative.  Those results also depend on proving
    [ExactOrderCriterion] for the bounded-search definition [Ord] under
    coprimality.  None of these conclusions is assumed or hidden in a
    predicate in this module. *)
End P090_OrbitOptimality.
Import P090_OrbitOptimality.

Module P090_WalkBridge.

Import ListNotations.
Local Open Scope Z_scope.

(** Finite-range sums.  These lemmas expose exactly the recursion used by
    [WalkExpSuffix], without assuming anything about the summands. *)

(** The exponent suffix consists of the current recursive call followed by
    the suffix beginning at the next exponent.  Both bounds are necessary:
    nonnegativity makes [Z.to_nat] preserve [next_e], and [next_e <= exponent]
    says that a head actually remains. *)

(** Structural facts about a selected prefix.  Positivity is conditional on
    positivity of the selected bases, because [PrefixSelected] itself does not
    state that the table is valid. *)

(** A constructor-facing version of [PrimePowerTransition].  The hard CRT,
    Euler-phi, and multiplicative-order facts are explicit premises rather
    than conclusions extracted from an already-built transition predicate. *)

(** Honest final boundary.  Completion of the C walk is kept separate from
    the mathematical orbit theorem.  The bridge asks for an actual catching
    set of the computed size and a lower bound for every catching set; it does
    not hide [Spec] in a loop invariant. *)

Definition WalkCompleted
    (pr pe : list Z) (x total : Z) : Prop :=
  total = WalkSuffix pr pe x 0 1.

Definition OrbitCoverUpperBound
    (m x cycle_count : Z) : Prop :=
  exists traps,
    CatchesAll m x traps /\
    Zlength traps = cycle_count + 1.

Definition OrbitCoverLowerBound
    (m x cycle_count : Z) : Prop :=
  forall traps,
    CatchesAll m x traps ->
    cycle_count + 1 <= Zlength traps.

End P090_WalkBridge.
Import P090_WalkBridge.

Module P090_TableBudget.

Import ListNotations.
Local Open Scope Z_scope.

(** A list-native view of [ValidFactorTable].  Keeping the ordering premise on
    every tail element makes the induction follow the actual nested walk. *)
Inductive OrderedPrimeTable : list Z -> list Z -> Prop :=
| ordered_prime_table_nil : OrderedPrimeTable [] []
| ordered_prime_table_cons : forall p exponent pr pe,
    IsPrime p ->
    1 <= exponent ->
    Forall (fun q => p < q) pr ->
    OrderedPrimeTable pr pe ->
    OrderedPrimeTable (p :: pr) (exponent :: pe).

(** The same recursion as [walk_suffix_lists], with the leaf contribution
    replaced by the full totient of the selected product. *)
Fixpoint enumerated_phi_sum (pr pe : list Z) (d : Z) : Z :=
  match pr, pe with
  | p :: pr', exponent :: pe' =>
      sum_nat_range 0 (S (Z.to_nat exponent))
        (fun k => enumerated_phi_sum pr' pe'
          (d * p ^ Z.of_nat k))
  | _, _ => EulerPhi d
  end.

Definition CoprimeToTable (d : Z) (pr : list Z) : Prop :=
  Forall (fun p => Z.gcd d p = 1) pr.

(** This module deliberately proves the table budget without proving that the
    enumerated products are all divisors.  The sole remaining bridge to the
    final optimality theorem is therefore orbit/divisor surjectivity, not a
    missing arithmetic fact about the C walk's cumulative bound. *)
End P090_TableBudget.
Import P090_TableBudget.

Module P090_DivisorEnumeration.

Import ListNotations.
Local Open Scope Z_scope.

(** Explicit exponent vectors and their products.  This relation follows the
    same head-first recursion as [walk_suffix_lists]. *)
Inductive ExponentTrace : list Z -> list Z -> list Z -> Z -> Prop :=
| exponent_trace_nil :
    ExponentTrace [] [] [] 1
| exponent_trace_cons : forall p pr maximum pe exponent exponents product,
    0 <= exponent <= maximum ->
    ExponentTrace pr pe exponents product ->
    ExponentTrace (p :: pr) (maximum :: pe) (exponent :: exponents)
      (Z.pow p exponent * product).

Fixpoint enumerated_products (pr pe : list Z) : list Z :=
  match pr, pe with
  | p :: pr', maximum :: pe' =>
      concat
        (map
           (fun n =>
              map (fun product => Z.pow p (Z.of_nat n) * product)
                (enumerated_products pr' pe'))
           (seq 0 (S (Z.to_nat maximum))))
  | _, _ => [1]
  end.

Fixpoint enumerated_walk_terms
    (pr pe : list Z) (x d : Z) : list Z :=
  match pr, pe with
  | p :: pr', maximum :: pe' =>
      concat
        (map
           (fun n =>
              enumerated_walk_terms pr' pe' x
                (d * Z.pow p (Z.of_nat n)))
           (seq 0 (S (Z.to_nat maximum))))
  | _, _ => [CycleTerm x d]
  end.

Definition NonUnitDivisorCycleSum
    (pr pe : list Z) (x : Z) : Z :=
  fold_right Z.add 0
    (map (CycleTerm x)
      (filter (fun d => negb (Z.eqb d 1))
        (enumerated_products pr pe))).

(** A durable choice history for the existing forward [PrefixSelected]
    relation. *)
Inductive PrefixSelectedTrace (pr pe : list Z) :
    Z -> list Z -> Z -> Prop :=
| prefix_selected_trace_zero :
    PrefixSelectedTrace pr pe 0 [] 1
| prefix_selected_trace_step : forall i exponents d exponent,
    PrefixSelectedTrace pr pe i exponents d ->
    0 <= i < Zlength pr ->
    0 <= exponent <= Znth i pe 0 ->
    PrefixSelectedTrace pr pe (i + 1) (exponents ++ [exponent])
      (d * Z.pow (Znth i pr 0) exponent).

End P090_DivisorEnumeration.
Import P090_DivisorEnumeration.

Module P090_DivisorCompleteness.

Import ListNotations.
Local Open Scope Z_scope.
Import P090_OrderFoundations.P090_OrderFoundations.

(** A recursive form of the prime-power table facts needed by unique
    factorization.  The last conjunct is precisely the coprimality boundary
    between the head prime and the remaining table product. *)
Inductive CanonicalFactorTable : list Z -> list Z -> Prop :=
| canonical_factor_table_nil :
    CanonicalFactorTable [] []
| canonical_factor_table_cons : forall p pr exponent pe,
    prime p ->
    1 <= exponent ->
    CanonicalFactorTable pr pe ->
    ~ (p | factor_product pr pe) ->
    CanonicalFactorTable (p :: pr) (exponent :: pe).

(** Strip from a divisor exactly the power of [p] available in the ambient
    factor [p^maximum * rest]. *)
Fixpoint enumerated_exponent_vectors (pe : list Z) : list (list Z) :=
  match pe with
  | [] => [[]]
  | maximum :: pe' =>
      concat
        (map
          (fun n => map (cons (Z.of_nat n))
            (enumerated_exponent_vectors pe'))
          (seq 0 (S (Z.to_nat maximum))))
  end.

Fixpoint exponent_vector_product (pr exponents : list Z) : Z :=
  match pr, exponents with
  | p :: pr', exponent :: exponents' =>
      Z.pow p exponent * exponent_vector_product pr' exponents'
  | _, _ => 1
  end.

End P090_DivisorCompleteness.
Import P090_DivisorCompleteness.

Module P090_OrderInputBridge.

Local Open Scope Z_scope.

Module ETI := euler_theorem_inverse_lib.

Import P090_OrderExcess.P090_OrderExcess.
Import P090_OrderExact.P090_OrderExact.

(** The search proof does not need an already-established [OrderInput].
    A positive terminal exponent whose power is one is enough.  Keeping this
    constructor separate avoids assuming [Ord | EulerPhi] in order to prove
    that very fact. *)
(** This is the non-circular producer contract needed by every caller of the
    C [order] helper. *)
End P090_OrderInputBridge.
Import P090_OrderInputBridge.

Module P090_FactorConsumer.

Local Open Scope Z_scope.
Import ListNotations.

Import P090_OrderExcess.P090_OrderExcess.
Import P090_OrderFoundations.P090_OrderFoundations.

(** The active division loop must retain the ordering history of the prefix.
    The old [FactorAtPrime] contained only [FactorPrefix], which is insufficient
    to reconstruct the strict, duplicate-free table at loop exit. *)
Definition StrictTrialState
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  StrictFactorPrefix m candidate remainder pr pe.

Definition StrictFactorAtPrime
    (m candidate original_remainder remainder exponent : Z)
    (pr pe : list Z) : Prop :=
  StrictFactorPrefix m candidate original_remainder pr pe /\
  IsPrime candidate /\
  original_remainder mod candidate = 0 /\
  0 <= exponent /\
  original_remainder = Z.pow candidate exponent * remainder /\
  0 < remainder <= original_remainder.

(** The exact loop-control formulation: a failed square guard produces the
    complete table, with the residual appended precisely when it is nonunit. *)
End P090_FactorConsumer.
Import P090_FactorConsumer.

Module P090_FactorMachineBounds.

Import ListNotations.
Local Open Scope Z_scope.

Definition FactorInputLimit : Z := 100000000000000.
Definition FactorCandidateGuardLimit : Z := 10000000.
Definition FactorCandidateStateLimit : Z := 10000001.
Definition Signed64Max : Z := 9223372036854775807.

(** [StrictTrialState] alone intentionally permits arbitrary candidates once
    the residual is one.  The executable loop does not: every advance occurs
    only after a successful square guard.  This staging predicate records the
    resulting consumer-visible frontier bound. *)
Definition FactorMachineTrialState
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  StrictTrialState m candidate remainder pr pe /\
  m <= FactorInputLimit /\
  candidate <= FactorCandidateStateLimit.

Definition FactorMachineAtPrime
    (m candidate original remainder exponent : Z)
    (pr pe : list Z) : Prop :=
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe /\
  m <= FactorInputLimit /\
  candidate <= FactorCandidateGuardLimit.

(** The strengthened state is mapped at every C transition that changes the
    factor frontier: base, guarded skip, guarded factor entry, division step,
    completed-prime return, and failed-square finalisation.  No unrestricted
    [StrictTrialState -> candidate bound] lemma is stated because it is false
    once the residual is one. *)
End P090_FactorMachineBounds.
Export P090_FactorMachineBounds.

Module P090_OrderConsumer.

Local Open Scope Z_scope.

Import P090_OrderExcess.P090_OrderExcess.
Import P090_OrderFoundations.P090_OrderFoundations.
Import P090_OrderExact.P090_OrderExact.

(** Consumer-facing wrappers discharge every abstract mathematical-law
    argument of the order-state transition library.  Consequently the C
    annotation needs only the current state and the facts produced by the
    tested branch. *)

End P090_OrderConsumer.
Import P090_OrderConsumer.

Module P090_WalkConsumer.

Import ListNotations.
Local Open Scope Z_scope.

(** A returned recursive call consumes exactly the current head term and
    therefore advances the durable pending-state index by one. *)
End P090_WalkConsumer.
Import P090_WalkConsumer.

Module P090_WalkCallBudget.

Import ListNotations.
Local Open Scope Z_scope.

(** A cumulative budget for [head + tail] supplies both the recursive-call
    budget for [head] and, after that exact call returns, the continuation
    budget for [tail]. *)
(** At entry to a nonterminal [walk] frame, exponent zero is the first C
    recursive call.  The unconsumed work is exactly the exponent suffix
    beginning at one. *)
(** Each exponent-loop iteration exposes exactly one recursive call.  The
    current accumulator funds that head call, and the returned accumulator
    funds the remaining exponent suffix. *)
(** The current predicates already expose exactly the cumulative facts used
    above: [WalkPendingState] retains both the whole-frame conservation
    equation and the budget for every unconsumed exponent.  No strengthening
    of the annotation predicate is required for recursive-call extraction. *)
End P090_WalkCallBudget.
Import P090_WalkCallBudget.

Module P090_PrimePowerConsumer.

Import ListNotations.
Local Open Scope Z_scope.

(** The theorem above closes the consumer-facing transition without assuming
    a final [Spec] fact.  Its only table-specific ingredients are the exact
    indexed prime power, the selected-prefix coprimality boundary, and the
    factor-product divisibility proved in this module. *)
End P090_PrimePowerConsumer.
Import P090_PrimePowerConsumer.

Module P090_WalkExponentConsumer.

Local Open Scope Z_scope.

(** The C exponent loop starts immediately after the exponent-zero recursive
    call.  The table entry supplies both primality and the positive maximum
    exponent; exact divisibility supplies the machine bound on [p]. *)
(** Multiplying the running prime power is exact at every taken iteration. *)
(** This is the exact branch expression used by the C assignment to [ph]. *)
Definition WalkExponentPhiUpdate
    (p exponent ph : Z) : Z :=
  if Z.eqb exponent 1 then p - 1 else ph * p.

(** A positive divisor of [m] is at most [m].  Stating this separately keeps
    the no-overflow premise visible rather than hiding it in the loop state. *)
(** Consumer-driven preservation theorem for one taken C-loop iteration.
    The indexed table supplies the exact divisibility that makes both
    multiplications mathematical (hence non-wrapping), while primality gives
    the Euler-phi update. *)
(** The two branch-specialized forms match the C conditional assignment
    without leaving an [if] for symbolic execution to normalize. *)
(** Projections after the body, in exactly the form expected by
    [prime_power_consumer_transition]. *)
(** Complete handoff from the exponent-state invariant to the packaged
    divisor/order transition used immediately before the recursive call. *)
(** On a failed loop guard, the state index is exactly one past the table
    exponent.  Its [pk]/[ph] values therefore describe the complete table
    prime power and remain machine-bounded. *)
(** Composition with the cumulative walk invariant at the same failed guard. *)
End P090_WalkExponentConsumer.
Import P090_WalkExponentConsumer.

Module P090_OrbitQuotient.

Import ListNotations.
Local Open Scope Z_scope.

Module OrderExact := P090_OrderExact.P090_OrderExact.

(** A forward-orbit hit is deliberately kept separate from any quotient
    representation.  This is exactly the witness exposed by [CatchesAll]. *)

Definition OrbitHit (m x start room : Z) : Prop :=
  exists time, 0 <= time /\
    room = (start * x ^ time) mod m.

(** [OrbitSeparated] is the consumer-facing uniqueness condition.  It says
    that two listed representatives cannot reach a common room.  Unlike a
    bare pairwise inequality, this is precisely what is needed to inject the
    representatives into an arbitrary catching list. *)

Definition OrbitSeparated
    (m x : Z) (representatives : list Z) : Prop :=
  forall left right room,
    In left representatives ->
    In right representatives ->
    OrbitHit m x left room ->
    OrbitHit m x right room ->
    left = right.

Definition OrbitCoversRange
    (m x : Z) (representatives : list Z) : Prop :=
  forall start,
    0 <= start < m ->
    exists representative,
      In representative representatives /\
      OrbitHit m x start representative.

Definition OrbitRepresentativeSystem
    (m x : Z) (representatives : list Z) : Prop :=
  NoDup representatives /\
  Forall (fun room => 0 <= room < m) representatives /\
  OrbitCoversRange m x representatives /\
  OrbitSeparated m x representatives.

(** A constructive finite pigeonhole lemma.  No choice function is used:
    at the induction step one concrete witness is removed from [targets]. *)

(** Thus a concrete representative system of the divisor-cycle size closes
    both halves of the minimisation specification. *)

(** The exact bounded-search result now discharges the order premise used by
    the earlier orbit lemmas. *)

(** Quotients are formed separately inside a gcd stratum.  This prevents the
    false conclusion that every residue has the global unit-orbit length. *)

Definition StratumCovers
    (m x gcd_value : Z) (representatives : list Z) : Prop :=
  forall start,
    0 <= start < m ->
    Z.gcd start m = gcd_value ->
    exists representative,
      In representative representatives /\
      OrbitHit m x start representative.

Definition StratumRepresentativeSystem
    (m x gcd_value : Z) (representatives : list Z) : Prop :=
  NoDup representatives /\
  Forall
    (fun room => 0 <= room < m /\ Z.gcd room m = gcd_value)
    representatives /\
  StratumCovers m x gcd_value representatives /\
  OrbitSeparated m x representatives.

(** The zero stratum is the exceptional one-point orbit, explaining the
    [+1] convention in [CycleAnswer]. *)

(** A single nonzero quotient block is completely explicit.  Its indices are
    the half-open interval [0, Ord), so the list can be counted without any
    quotient choice. *)

Definition UnitOrbitList
    (modulus x unit : Z) : list Z :=
  map
    (fun index : nat =>
       (unit * x ^ Z.of_nat index) mod modulus)
    (seq 0 (Z.to_nat (Ord x modulus))).

(** A no-choice finite quotient constructor.  The representative of an item
    is the first related element of the fixed universe, and [nodup] keeps one
    copy of each such canonical key. *)

Definition EquivalenceLaws (relation : Z -> Z -> Prop) : Prop :=
  (forall item, relation item item) /\
  (forall left right, relation left right -> relation right left) /\
  (forall left middle right,
      relation left middle -> relation middle right -> relation left right).

Definition CanonicalKey
    (relatedb : Z -> Z -> bool) (universe : list Z) (item : Z) : Z :=
  match find (relatedb item) universe with
  | Some representative => representative
  | None => 0
  end.

Definition FiniteQuotient
    (relatedb : Z -> Z -> bool) (universe : list Z) : list Z :=
  nodup Z.eq_dec (map (CanonicalKey relatedb universe) universe).

(** Every forward hit from a unit is represented by the bounded list: reduce
    its time modulo the exact order, then use the explicit index. *)

(** Consequently the explicit block contains exactly the forward orbit and
    has cardinality [Ord]. *)

Definition UnitOrbitRelatedb
    (modulus x left right : Z) : bool :=
  existsb (Z.eqb right) (UnitOrbitList modulus x left).

(** Exact remaining quotient boundary.

    The lemmas above finish the constructive pigeonhole argument and the
    final [Spec] bridge once a representative list is available.  What is
    still missing is the following *theorem*, which is intentionally not
    declared as an axiom or predicate field:

      For every divisor [d >= 2] of [m], under [OrderInput (x mod d) d
      (EulerPhi d)], construct a list of representatives for the gcd-[m/d]
      stratum modulo [m], prove [OrbitSeparated], and prove its length is
      [EulerPhi d / Ord (x mod d) d].

    The no-choice enumeration mechanism itself is now complete:
    [FiniteQuotient] takes the first related item as a canonical key and its
    coverage and separation are proved above.  The concrete unit-orbit
    decision procedure [UnitOrbitRelatedb] is also proved correct, forward
    hits are symmetric/transitive on units, and [UnitOrbitList] proves that
    every class is duplicate-free with exact length [Ord].

    The minimal missing cardinality theorem is therefore the finite partition
    statement obtained after restricting [FiniteQuotient] to the explicit
    list of unit residues:

      [Zlength unit_representatives * Ord (x mod d) d = EulerPhi d],

    proved by showing that
    [concat (map (UnitOrbitList d (x mod d)) unit_representatives)] is a
    permutation of that unit list.  This needs only the remaining bookkeeping
    that packages the equivalence laws on the unit-residue universe; neither
    class size nor representative selection is still a number-theory gap.
    Dividing the equality gives the requested quotient length.  After the
    elementary transport [u |-> (m/d)*u], concatenating all divisor strata
    with [zero_singleton_stratum_system] gives the full representative system,
    and [representative_system_implies_spec] closes solver optimality.  No
    statement above assumes this cardinality or transport result. *)
End P090_OrbitQuotient.
Import P090_OrbitQuotient.

Module P090_UnitOrbitPartition.

Import ListNotations.
Local Open Scope Z_scope.

Module ETI := euler_theorem_inverse_lib.

(** The finite domain used by Euler phi, converted from natural residues to
    integers.  For moduli at least two the last candidate [modulus] is
    filtered out, so this is exactly the half-open unit range. *)

Definition UnitResidue (modulus unit : Z) : Prop :=
  0 <= unit < modulus /\ Z.gcd unit modulus = 1.

Definition UnitResidueb (modulus unit : Z) : bool :=
  (0 <=? unit) && (unit <? modulus) &&
  Z.eqb (Z.gcd unit modulus) 1.

Definition UnitResidues (modulus : Z) : list Z :=
  map Z.of_nat
    (filter
      (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) modulus) 1)
      (seq 1 (Z.to_nat modulus))).

(** Guard the orbit relation outside the unit domain so that it is a genuine
    equivalence on all integers.  Inside the domain it is exactly forward
    reachability; outside it degenerates to equality. *)

Definition UnitOrbitEquiv
    (modulus x left right : Z) : Prop :=
  if UnitResidueb modulus left
  then UnitResidue modulus right /\ OrbitHit modulus x left right
  else left = right.

Definition UnitOrbitEquivb
    (modulus x left right : Z) : bool :=
  if UnitResidueb modulus left
  then UnitResidueb modulus right && UnitOrbitRelatedb modulus x left right
  else Z.eqb left right.

Definition UnitRepresentatives (modulus x : Z) : list Z :=
  FiniteQuotient
    (UnitOrbitEquivb modulus x)
    (UnitResidues modulus).

(** The orbit blocks of distinct canonical representatives are disjoint. *)

Definition UnitOrbitBlocks (modulus x : Z) : list Z :=
  concat
    (map (UnitOrbitList modulus x)
      (UnitRepresentatives modulus x)).

Definition UnitOrbitRepresentativeSystem
    (modulus x : Z) (representatives : list Z) : Prop :=
  StratumRepresentativeSystem modulus x 1 representatives.

(** Consumer-facing reduced-base package used by each nonzero divisor
    stratum of the solver. *)

End P090_UnitOrbitPartition.
Import P090_UnitOrbitPartition.

Module P090_GcdStratumTransport.

Import ListNotations.
Local Open Scope Z_scope.

Module OQ := P090_OrbitQuotient.
Module OE := P090_OrderExact.P090_OrderExact.

Definition StratumLift (m d unit : Z) : Z :=
  (m / d) * unit.

Definition StratumProject (m d room : Z) : Z :=
  room / (m / d).

Definition LiftedRepresentatives
    (m d : Z) (representatives : list Z) : list Z :=
  map (StratumLift m d) representatives.

(** A unit representative system is exactly the gcd-one stratum system in
    the quotient modulus.  Transporting it produces the gcd-[m/d] stratum
    system in the original modulus, preserving its cardinality. *)
(** Divisor one is the zero stratum: its sole unit residue is zero, and its
    lift is the unique room whose gcd with [m] is [m]. *)
End P090_GcdStratumTransport.
Import P090_GcdStratumTransport.

Module P090_DivisorCycleBridge.

Import ListNotations.
Local Open Scope Z_scope.

(** A concrete finite list of the positive divisors of [m].  The enumeration
    starts at one and ends at [m], so zero never reaches the remainder test. *)
Definition positive_divisor_list (m : Z) : list Z :=
  filter
    (fun d => Z.eqb (m mod d) 0)
    (map Z.of_nat (seq 1 (Z.to_nat m))).

Definition ConcreteNonUnitDivisorCycleSum (m x : Z) : Z :=
  fold_right Z.add 0
    (map (CycleTerm x)
      (filter (fun d => negb (Z.eqb d 1))
        (positive_divisor_list m))).

Definition RoomZeroCycleTotal (m x : Z) : Z :=
  1 + ConcreteNonUnitDivisorCycleSum m x.

(** The concrete list contains divisor one, but [CycleTerm] assigns it zero.
    This is the exact full-divisor formulation of the same walk sum. *)
End P090_DivisorCycleBridge.
Import P090_DivisorCycleBridge.

Module P090_GlobalOrbitBridge.

Import ListNotations.
Local Open Scope Z_scope.

(** This alignment predicate is the reusable consumer interface for later
    stratum constructors.  It asks only for a proved representative system
    at each gcd value; it does not prescribe how that system was built. *)
Definition AlignedStratumSystems
    (m x : Z) (gcd_values : list Z) (blocks : list (list Z)) : Prop :=
  Forall2
    (fun gcd_value representatives =>
       StratumRepresentativeSystem m x gcd_value representatives)
    gcd_values blocks.

Definition ExactNonUnitDivisorSystems
    (m x : Z) (divisors : list Z) (blocks : list (list Z)) : Prop :=
  Forall2
    (fun divisor representatives =>
       1 < divisor /\
       (divisor | m) /\
       StratumRepresentativeSystem
         m x (m / divisor) representatives /\
       Zlength representatives = CycleTerm x divisor)
    divisors blocks.

Definition ExactZeroStratumSystem
    (m x : Z) (zero_block : list Z) : Prop :=
  StratumRepresentativeSystem m x m zero_block /\
  Zlength zero_block = 1.

(** Every room is classified either into the zero gcd stratum [m], or into
    one of the explicitly supplied nonunit divisor strata. *)
Definition DivisorStrataClassify
    (m : Z) (divisors : list Z) : Prop :=
  forall start,
    0 <= start < m ->
    Z.gcd start m = m \/
    exists divisor,
      In divisor divisors /\
      Z.gcd start m = m / divisor.

Definition DistinctGlobalStratumKeys
    (m : Z) (divisors : list Z) : Prop :=
  NoDup (m :: map (fun divisor => m / divisor) divisors).

(** Specialisation to the exact divisor list used by the executable walk.
    The later transport/partition modules need only instantiate the four
    explicit interfaces above; all concatenation, disjointness, counting,
    catching, and universal lower-bound work is complete here. *)
End P090_GlobalOrbitBridge.
Import P090_GlobalOrbitBridge.

Module P090_DivisorStrataKeys.

Import ListNotations.
Local Open Scope Z_scope.

Definition concrete_nonunit_divisors (m : Z) : list Z :=
  filter (fun divisor => negb (Z.eqb divisor 1))
    (positive_divisor_list m).

(** These are exactly the two concrete, purely arithmetic premises consumed
    by [concrete_divisor_strata_imply_spec].  Later orbit modules therefore
    need only supply the exact per-stratum representative systems. *)
End P090_DivisorStrataKeys.
Import P090_DivisorStrataKeys.

Module P090_FinalOrbitInstantiation.

Import ListNotations.
Local Open Scope Z_scope.

Definition ConcreteZeroBlock (m : Z) : list Z :=
  LiftedRepresentatives m 1 [0].

Definition ConcreteNonUnitBlock
    (m x divisor : Z) : list Z :=
  LiftedRepresentatives m divisor
    (UnitRepresentatives divisor (x mod divisor)).

Definition ConcreteNonUnitBlocks
    (m x : Z) : list (list Z) :=
  map (ConcreteNonUnitBlock m x)
    (concrete_nonunit_divisors m).

(** The C expression returns the accumulated divisor sum before adding the
    distinguished zero-room contribution.  This commuted form matches that
    source-level expression without asking symbolic execution to normalize
    the addition order. *)
(** Direct consumer wrapper for the state carried by the top-level walk. *)
(** This is the complete non-circular mathematical endpoint needed by the C
    walk: factor-table enumeration determines the sum, while the concrete
    orbit construction proves that the same value is globally optimal. *)
End P090_FinalOrbitInstantiation.
Import P090_FinalOrbitInstantiation.
