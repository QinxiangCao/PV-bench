/*
 * Sort a contiguous row-major matrix of decimal digits in descending greedy
 * order.  Row i starts at numbers + i * number_width, and lengths[i] records
 * the number of valid digits in that row.
 */
void quicksort_numbers(int *numbers, int *lengths, int count,
                       int number_width, int low, int high)

{
    if (0 <= low && low < high && high < count) {
        int pivot_length = lengths[high];
        int boundary = low - 1;
        int scan;
        int pivot;

        for (scan = low; scan < high; ++scan) {
            int current_length = lengths[scan];
            int total_length = current_length + pivot_length;
            int comparison = 0;
            int position;

            /* Compare current+pivot with pivot+current without constructing
             * either temporary concatenation. */

            for (position = 0; position < total_length; ++position) {
                int left_digit;
                int right_digit;

                if (position < current_length) {

                    left_digit = numbers[scan * number_width + position];
                } else {

                    left_digit = numbers[high * number_width +
                                         (position - current_length)];
                }

                if (position < pivot_length) {

                    right_digit = numbers[high * number_width + position];
                } else {

                    right_digit = numbers[scan * number_width +
                                          (position - pivot_length)];
                }

                if (left_digit != right_digit) {
                    comparison = left_digit - right_digit;
                    break;
                }
            }

            if (comparison > 0) {
                int column;
                int temporary_length;

                ++boundary;

                for (column = 0; column < number_width; ++column) {

                    int temporary_digit =
                        numbers[boundary * number_width + column];
                    numbers[boundary * number_width + column] =
                        numbers[scan * number_width + column];
                    numbers[scan * number_width + column] = temporary_digit;
                }

                temporary_length = lengths[boundary];
                lengths[boundary] = lengths[scan];
                lengths[scan] = temporary_length;
            }

        }

        pivot = boundary + 1;

        for (int column = 0; column < number_width; ++column) {

            int temporary_digit =
                numbers[pivot * number_width + column];
            numbers[pivot * number_width + column] =
                numbers[high * number_width + column];
            numbers[high * number_width + column] = temporary_digit;
        }

        lengths[high] = lengths[pivot];
        lengths[pivot] = pivot_length;

        if (pivot > low) {
            quicksort_numbers(numbers, lengths, count, number_width,
                              low, pivot - 1) ;

            if (pivot < high) {
                quicksort_numbers(numbers, lengths, count, number_width,
                                  pivot + 1, high) ;
            }
        } else if (pivot < high) {
            quicksort_numbers(numbers, lengths, count, number_width,
                              pivot + 1, high) ;
        }
    }
}

/*
 * numbers contains count rows of number_width integer cells.  Each row holds
 * one positive integer as decimal digits in 0..9.  result receives the largest
 * possible concatenation and the return value is result itself.
 */
int* concatenating_numbers(int *numbers, int count, int number_width,
                          int *lengths, int *result)

{
    int result_length = 0;
    int i;

    if (count > 1) {
        quicksort_numbers(numbers, lengths, count, number_width,
                          0, count - 1) ;
    }

    for (i = 0; i < count; ++i) {
        int j;

        for (j = 0; j < lengths[i]; ++j) {

            result[result_length] = numbers[i * number_width + j];
            ++result_length;
        }
    }

    return result;
}
