/*@ Extern Coq (sum : list Z -> Z) 
               (sublist : {A} -> Z -> Z -> list A -> list A)
               (IntArray::full : Z -> Z -> list Z -> Assertion)
               (IntArray::missing_i: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (store_array_box: Z -> Z -> list Z -> Assertion)
               (store_array_box_array: Z -> list Z -> Assertion)
               (IntArray::seg: Z -> Z -> Z -> list Z -> Assertion)
               (IntArray::seg_shape: Z -> Z -> Z -> Assertion)
               (IntArray::full_shape: Z -> Z -> Assertion)
               (IntArray::missing_i_shape : Z -> Z -> Z -> Z -> Assertion)
               (IntArray::undef_full : Z -> Z -> Assertion)
               (IntArray::undef_seg: Z -> Z -> Z -> Assertion)
               (IntArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
               (zeros: Z -> list Z)
*/

/*@ include strategies "int_array.strategies" */


/*@ Extern Coq (UIntArray::missing_i: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (UIntArray::seg: Z -> Z -> Z -> list Z -> Assertion)
               (UIntArray::full: Z -> Z -> list Z -> Assertion)
               (UIntArray::seg_shape: Z -> Z -> Z -> Assertion)
               (UIntArray::full_shape: Z -> Z -> Assertion)
               (UIntArray::missing_i_shape : Z -> Z -> Z -> Z -> Assertion)
               (UIntArray::undef_seg: Z -> Z -> Z -> Assertion)
               (UIntArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (UIntArray::undef_full : Z -> Z -> Assertion)
*/
/*@ include strategies "uint_array.strategies" */
/*@ include strategies "undef_uint_array.strategies"*/
/*@ include strategies "array_shape.strategies" */