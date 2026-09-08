import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace Algorithms.concatenating_numbers.lean

open AUXLib

def number_item : Type := List Int × Int

def item_digits (x : number_item) : List Int :=
  sublist 0 (Prod.snd x) (Prod.fst x)

def paired_items (rows : List (List Int)) (lengths : List Int) :
  List number_item :=
  List.zip rows lengths

def concatenate_items (items : List number_item) : List Int :=
  List.flatten (List.map item_digits items)

def concatenate_rows (rows : List (List Int)) (lengths : List Int) :
  List Int :=
  concatenate_items (paired_items rows lengths)

def digit_lex_ge (xs ys : List Int) : Prop :=
  Zlength xs = Zlength ys ∧
  (xs = ys ∨
   ∃ k, (0 ≤ k ∧ k < Zlength xs) ∧
     (∀ j, (0 ≤ j ∧ j < k) → Znth j xs 0 = Znth j ys 0) ∧
     Znth k ys 0 < Znth k xs 0)

def RowsWellFormed
    (rows : List (List Int)) (lengths : List Int)
    (count width : Int) : Prop :=
  Zlength rows = count ∧
  Zlength lengths = count ∧
  (∀ i, (0 ≤ i ∧ i < count) →
     Zlength (Znth i rows []) = width ∧ (1 ≤ Znth i lengths 0 ∧ Znth i lengths 0 ≤ width) ∧ (1 ≤ Znth 0 (Znth i rows []) 0 ∧ Znth 0 (Znth i rows []) 0 ≤ 9) ∧
     (∀ j, (0 ≤ j ∧ j < Znth i lengths 0) → (0 ≤ Znth j (Znth i rows []) 0 ∧ Znth j (Znth i rows []) 0 ≤ 9) ))

def FlatRows
    (flat : List Int) (rows : List (List Int)) (count width : Int) : Prop :=
  Zlength flat = count * width ∧
  Zlength rows = count ∧
  ∀ i, (0 ≤ i ∧ i < count) →
    Znth i rows [] = sublist (i * width) ((i + 1) * width) flat

def PairedPermutation
    (rows lengths_rows : List (List Int))
    (lens lengths_lens : List Int) : Prop :=
  Zlength rows = Zlength lens ∧
  Zlength lengths_rows = Zlength lengths_lens ∧
  Permutation (paired_items rows lens)
              (paired_items lengths_rows lengths_lens)

def LargestConcatenation
    (original_rows arranged_rows : List (List Int))
    (original_lens arranged_lens output : List Int) : Prop :=
  PairedPermutation original_rows arranged_rows
                    original_lens arranged_lens ∧
  output = concatenate_rows arranged_rows arranged_lens ∧
  ∀ alternative_rows alternative_lens,
    PairedPermutation original_rows alternative_rows
                      original_lens alternative_lens →
    digit_lex_ge output
      (concatenate_rows alternative_rows alternative_lens)

end Algorithms.concatenating_numbers.lean
