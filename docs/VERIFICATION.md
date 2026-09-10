# Verification model

PV-Bench combines QCP's automatic verification of annotated C with Rocq or Lean 4 proofs of the remaining obligations. This document explains the workflow and what the released artifacts establish. For the benchmark tasks and setup, see the [README](../README.md).

## What QCP verifies

[QCP](https://www.qua.codes/en/index.html) — *Qualified C Programming* — reasons about C programs under explicit specifications. 
A function contract states what must hold before a call (`Require`) and what must hold when it returns (`Ensure`). 
The guarantee is relative to these preconditions and the modeled C semantics; it is not a claim that the program behaves correctly for arbitrary inputs or that the formal specification captures every intention in the natural-language problem.

## From annotations to proof obligations

1. **Describe the program's intended behavior and memory.** Contracts use mathematical values and predicates to describe both results and the heap. 
   QCP uses *separation logic*: an assertion such as `P * Q` describes disjoint portions of memory, allowing specifications to express which cells, arrays or data structures a function can access. Loop invariants
   describe what remains true across iterations; helper-function contracts  and intermediate assertions supply additional reasoning steps. 
   See the [annotation tutorial](https://www.qua.codes/en/tutorials/index.html).

2. **Symbolically execute and generate verification conditions (VCs).** QCP tracks symbolic values and memory assertions through the annotated code. 
   It generates obligations showing that one assertion entails another—for example, that a function's final state satisfies its postcondition. 
   For a loop, QCP uses the supplied invariant to reason about an arbitrary iteration. It generates obligations showing that the invariant holds initially and is preserved across iterations.
   Safety obligations cover operations such as memory accesses, division and signed arithmetic.
   Finishing symbolic execution does not by itself establish that every obligation is proved.
   See the tutorials on [VCs](https://www.qua.codes/en/tutorials/t3-3.html) and [loops](https://www.qua.codes/en/tutorials/t3-6.html).

3. **Discharge automatic obligations and prove the remainder.** QCP's automatic entailment solver combines rule-based separation-logic reasoning about memory with a lightweight SMT solver for pure logical and arithmetic constraints. 
   User-defined predicates can be supported by strategy rules, whose soundness also requires proofs. Obligations outside this automation are exported for proof in **Rocq** or **Lean 4**, using the corresponding mathematical definitions and libraries. 
   See the [QCP tool paper](https://vexoben.github.io/files/qcp-tase2026.pdf), [strategy tutorial](https://www.qua.codes/en/tutorials/t4-3.html) and [Lean-backend release notes](https://www.qua.codes/en/releases/qcp-v2-1-0.html).

This division gives PV-Bench its three tasks: write the **contract** (T1), supply the **annotations** needed for verification (T2), and prove the **residual obligations** (T3).

## Automatic results and residual proofs

In the current PV-Bench artifacts, `proof_auto` records the obligations discharged by QCP's automatic reasoning. The exported statements use Rocq's `Admitted` or Lean's `sorry` because proof certificates for those results have not yet been exported. These entries identify work already completed by QCP, rather than work left for the manual-proof task.

During backend compilation, Rocq or Lean treats these statements as trusted facts supplied by QCP; it does not independently check a proof of each automatic result.

The residual obligations are handled in `proof_manual` and checked by the chosen proof assistant, relative to the imported definitions and assumptions. 
The verification model therefore combines trust in QCP's VC generation and automatic reasoning with proof-assistant checking of the residual proofs.

## What compiling `goal_check` establishes

`goal_check` combines `proof_auto` and `proof_manual` and checks that their declarations match the complete set of generated verification conditions.

For T3, the generated goals and `proof_auto` are fixed inputs. The candidate must prove every obligation assigned to `proof_manual`, without `Admitted`, `admit`, `sorry`, or additional axioms in either the submitted proofs or their supporting lemmas. These proofs may use the fixed backend libraries and QCP-established automatic results.

A valid answer must satisfy both requirements: `goal_check` compiles successfully, and every required manual obligation has a proof meeting these restrictions. Compilation alone does not enforce the absence of admissions or additional axioms.
