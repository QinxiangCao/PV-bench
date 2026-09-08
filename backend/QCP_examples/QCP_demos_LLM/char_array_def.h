/*@ Extern Coq (CharArray::full : Z -> Z -> list Z -> Assertion)
               (CharArray::missing_i: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (CharArray::seg: Z -> Z -> Z -> list Z -> Assertion)
               (CharArray::undef_full: Z -> Z -> Assertion)
               (CharArray::undef_seg: Z -> Z -> Z -> Assertion)
               (CharArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
               (repeat_Z: {A} -> A -> Z -> list A)
*/

/*@ include strategies "char_array.strategies" */
