import AUXLib.ListLib
import AUXLib.Prime

namespace Algorithms.integer_divide.lean

open AUXLib
export AUXLib.Prime (prime)

inductive HdRel {A : Type u} (R : A → A → Prop) (a : A) : List A → Prop where
  | HdRel_nil : HdRel R a []
  | HdRel_cons (b : A) (l : List A) : R a b → HdRel R a (b :: l)

inductive Sorted {A : Type u} (R : A → A → Prop) : List A → Prop where
  | Sorted_nil : Sorted R []
  | Sorted_cons (a : A) (l : List A) : Sorted R l → HdRel R a l → Sorted R (a :: l)

def PrimeFactorization (original : Int) (factors : List Int) : Prop :=
  Forall prime factors ∧ Sorted (· ≤ ·) factors ∧
  factors.foldr (· * ·) 1 = original ∧
  ∀ q : Int, q ∈ factors ↔ prime q ∧ Z.divide q original

end Algorithms.integer_divide.lean
