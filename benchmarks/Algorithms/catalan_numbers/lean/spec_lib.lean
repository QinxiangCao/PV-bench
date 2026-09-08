import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.catalan_numbers.lean

open AUXLib

def stack_run (depth : Nat) (ops : List Bool) : Option Nat :=
  match ops with
  | [] => some depth
  | true :: rest => stack_run (depth + 1) rest
  | false :: rest => match depth with
    | 0 => none
    | depth' + 1 => stack_run depth' rest

def stack_push_count : List Bool → Nat
  | [] => 0
  | true :: rest => stack_push_count rest + 1
  | false :: rest => stack_push_count rest

def all_stack_words : Nat → List (List Bool)
  | 0 => [[]]
  | len + 1 => (all_stack_words len).map (true :: ·) ++ (all_stack_words len).map (false :: ·)

def legal_stack_completion_nat (pushes depth : Nat) (ops : List Bool) : Prop :=
  ops.length = 2 * pushes + depth ∧ stack_push_count ops = pushes ∧
  stack_run depth ops = some 0

def legal_stack_completionb (pushes depth : Nat) (ops : List Bool) : Bool :=
  (ops.length == 2 * pushes + depth) && (stack_push_count ops == pushes) &&
  match stack_run depth ops with | some 0 => true | _ => false

def stack_completion_set (pushes depth : Nat) : List (List Bool) :=
  (all_stack_words (2 * pushes + depth)).filter (legal_stack_completionb pushes depth)

def LegalStackCompletion (pushes depth : Int) (ops : List Bool) : Prop :=
  0 ≤ pushes ∧ 0 ≤ depth ∧ legal_stack_completion_nat pushes.toNat depth.toNat ops

def LegalStackBehavior (pushes : Int) (ops : List Bool) : Prop := LegalStackCompletion pushes 0 ops

def StackSequenceSet (pushes : Int) : List (List Bool) := stack_completion_set pushes.toNat 0

def StackCompletionCount (pushes depth value : Int) : Prop :=
  0 ≤ pushes ∧ 0 ≤ depth ∧ value = Int.ofNat (stack_completion_set pushes.toNat depth.toNat).length

def StackSequenceCount (pushes value : Int) : Prop :=
  0 ≤ pushes ∧ value = Int.ofNat (StackSequenceSet pushes).length ∧
  ∀ ops, ops ∈ StackSequenceSet pushes ↔ LegalStackBehavior pushes ops

def StackCellIndex (n row col : Int) : Int := row * (n + 1) + col

def StackCellBound (row col value : Int) : Prop :=
  0 ≤ row ∧ 0 ≤ col ∧ 0 ≤ value ∧ value ≤ Z.pow 2 (2 * row + col)

def StackCellCorrect (n row col value : Int) : Prop :=
  row + col ≤ n → StackCompletionCount row col value

def StackTablePrefix (n : Int) (table : List Int) (written : Int) : Prop :=
  0 ≤ n ∧ (0 ≤ written ∧ Zlength table = written) ∧
  ∀ row col, (0 ≤ row ∧ row ≤ n) → (0 ≤ col ∧ col ≤ n) →
    (0 ≤ StackCellIndex n row col ∧ StackCellIndex n row col < written) →
    StackCellBound row col (Znth (StackCellIndex n row col) table 0) ∧
    StackCellCorrect n row col (Znth (StackCellIndex n row col) table 0)

def StackRowsDone (n : Int) (table : List Int) (rows_done : Int) : Prop :=
  0 ≤ rows_done ∧ StackTablePrefix n table (rows_done * (n + 1))

end Algorithms.catalan_numbers.lean
