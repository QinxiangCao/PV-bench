/*@ Extern Coq
      (sum : list Z -> Z)
      (Z::shiftl : Z -> Z -> Z)
      (RowsWellFormed : list (list Z) -> list Z -> Z -> Z -> Prop)
      (FlatRows : list Z -> list (list Z) -> Z -> Z -> Prop)
      (DPTablePrefix : list (list Z) -> list Z -> Z -> Z -> list Z -> Prop)
      (LargestConcatenation : list (list Z) -> list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.concatenating_numbers_dp.rocq.spec_lib */

/*
 * Compare the two possible orders left+right and right+left without building
 * either temporary concatenation.  A positive result means that left should
 * be placed before right in a largest concatenation.
 */
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

/*
 * Build the largest concatenation with subset dynamic programming.
 *
 * numbers contains count rows of number_width integer cells.  Row i stores
 * the decimal digits of one positive integer, and lengths[i] is the number of
 * valid cells in that row.  Digits are stored from most to least significant.
 *
 * best_first must contain at least 2^count integer cells.  For each nonempty
 * mask, best_first[mask] records an index that can be placed first in an
 * optimal concatenation of exactly the rows selected by mask.  Removing that
 * index produces the next subset state.  result must contain at least
 * sum(lengths[0..count)) cells and receives the answer as decimal digits.
 *
 * The exchange rule x+y >= y+x determines which of two rows may occur first
 * in an optimal answer.  Consequently, if bit is one selected index and rest
 * is the mask without bit, the transition is
 *
 *   best_first[mask] = better(bit, best_first[rest]).
 *
 * There are 2^count states.  Finding the selected bit takes at most count
 * steps, and each transition compares at most 2 * number_width digits, so the
 * running time is O(2^count * (count + number_width)).  The DP uses
 * O(2^count) integer cells.
 */
int *concatenating_numbers_dp(const int *numbers, int count, int number_width,
                              const int *lengths, int *best_first,
                              int *result)
/*@ With (rows : list (list Z)) (lens : list Z) (flat : list Z)
    Require
      1 <= count && count <= 20 &&
      1 <= number_width && number_width <= 10 &&
      2 <= Z::shiftl(1, count) && Z::shiftl(1, count) <= 1048576 &&
      1 <= sum(lens) && sum(lens) <= 200 &&
      RowsWellFormed(rows, lens, count, number_width) &&
      FlatRows(flat, rows, count, number_width) &&
      IntArray::full(numbers, count * number_width, flat) *
      IntArray::full(lengths, count, lens) *
      IntArray::undef_full(best_first, Z::shiftl(1, count)) *
      IntArray::undef_full(result, sum(lens))
    Ensure
      exists choices output,
        __return == result &&
        DPTablePrefix(rows, lens, count, Z::shiftl(1, count), choices) &&
        LargestConcatenation(rows, lens, output) &&
        Zlength(output) == sum(lens) &&
        IntArray::full(numbers, count * number_width, flat) *
        IntArray::full(lengths, count, lens) *
        IntArray::full(best_first, Z::shiftl(1, count), choices) *
        IntArray::full(result, sum(lens), output)
 */
{
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
