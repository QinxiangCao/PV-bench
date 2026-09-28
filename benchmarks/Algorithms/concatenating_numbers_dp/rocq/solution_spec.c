#include "array2_def.h"

/*@ Extern Coq
      (concat : {A} -> list (list A) -> list A)
      (DecimalRowValues : list (list Z) -> list Z -> list Z)
      (sum : list Z -> Z)
      (Z::shiftl : Z -> Z -> Z)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (hd : {A} -> A -> list A -> A)
      (concatenate_indices : list (list Z) -> list Z -> list Z -> list Z)
      (all_indices : Z -> list Z)
      (LargestConcatenation : list (list Z) -> list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.concatenating_numbers_dp.rocq.spec_lib */

int compare_concatenated_order(const int *numbers, const int *lengths,
                                      int number_width, int left, int right)

{
    int left_length = lengths[left];
    int right_length = lengths[right];
    int total_length = left_length + right_length;

    for (int position = 0; position < total_length; ++position) {
        int left_then_right;
        int right_then_left;

        if (position < left_length) {

            left_then_right = numbers[left * number_width + position];
        } else {

            left_then_right =
                numbers[right * number_width + position - left_length];
        }

        if (position < right_length) {

            right_then_left = numbers[right * number_width + position];
        } else {

            right_then_left =
                numbers[left * number_width + position - right_length];
        }

        if (left_then_right > right_then_left) {
            return 1;
        }
        if (left_then_right < right_then_left) {
            return -1;
        }
    }

    return 0;
}

int *concatenating_numbers_dp(const int *numbers, int count, int number_width,
                              const int *lengths,
                              int *result)
/*@ With (rows : list (list Z)) (lens : list Z) (flat : list Z)
    Require
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      2 <= Z::shiftl(1, count) && Z::shiftl(1, count) <= 1048576 &&
      1 <= sum(lens) && sum(lens) <= 200 &&
      Zlength(rows) == count &&
      Zlength(lens) == count &&
      Forall(eq(number_width), map(Zlength, rows)) &&
      Forall(Z::le(1), lens) &&
      Forall(Z::ge(number_width), lens) &&
      Forall(Z::le(1), map(hd(0), rows)) &&
      Forall(Z::ge(9), map(hd(0), rows)) &&
      Forall(Z::le(0), concatenate_indices(rows, lens, all_indices(Zlength(rows)))) &&
      Forall(Z::ge(9), concatenate_indices(rows, lens, all_indices(Zlength(rows)))) &&
      flat == concat(rows) &&
      Forall(Z::ge(1000000000), DecimalRowValues(rows, lens)) &&
      IntArray2::full(numbers, count, number_width, rows) *
      IntArray::full(lengths, count, lens) *
      IntArray::undef_full(result, sum(lens))
    Ensure
      exists output,
        __return == result &&
        LargestConcatenation(rows, lens, output) &&
        IntArray2::full(numbers, count, number_width, rows) *
        IntArray::full(lengths, count, lens) *
        IntArray::full(result, sum(lens), output)
 */
{
    int best_first[1048576];

    int state_count = 1 << count;

    best_first[0] = -1;

    for (int mask = 1; mask < state_count; ++mask) {
        int bit = 0;
        int bit_value = 1;

        while ((mask & bit_value) == 0) {
            ++bit;
            bit_value = bit_value << 1;
        }

        int rest = mask ^ bit_value;

        int previous_best = best_first[rest];

        if (previous_best < 0 ||
            compare_concatenated_order(numbers, lengths, number_width,
                                       bit, previous_best)  > 0) {
            best_first[mask] = bit;
        } else {
            best_first[mask] = previous_best;
        }

    }

    int mask = state_count - 1;
    int result_length = 0;

    while (mask != 0) {
        int first = best_first[mask];

        for (int position = 0; position < lengths[first]; ++position) {

            result[result_length] =
                numbers[first * number_width + position];
            ++result_length;
        }

        mask = mask ^ (1 << first);
    }

    return result;
}
