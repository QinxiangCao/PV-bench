/*@ Import Lean
import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
open AUXLib
open scoped SimpleC
*/
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
 */
/*@ Extern Coq
      (Sorting::increasing : list Z -> Prop)
 */

/*
 * Stable decimal-bucket radix sort for non-negative integers.
 * Each pass distributes the input by one decimal digit and writes the
 * buckets back in order.  Processing from right to left keeps a pass stable.
 */
void sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(input) == n &&
      (forall (i : Z),
         (0 <= i && i < n) =>
         (0 <= Znth(i, input, 0) && Znth(i, input, 0) <= 999999999)) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        Zlength(output) == n &&
        Permutation(input, output) &&
        Sorting::increasing(output) &&
        IntArray::full(a, n, output)
 */
{
    if (n <= 1) {
        return;
    }

    int max_value = a[0];

    for (int i = 1; i < n; ++i) {
        if (a[i] > max_value) {
            max_value = a[i];
        }
    }

    int output[1000];
    int count[10];

    for (int exponent = 1; max_value / exponent > 0; exponent *= 10) {

        for (int digit = 0; digit < 10; ++digit) {
            count[digit] = 0;
        }

        for (int i = 0; i < n; ++i) {
            int digit = (a[i] / exponent) % 10;

            ++count[digit];
        }

        for (int digit = 1; digit < 10; ++digit) {
            count[digit] += count[digit - 1];
        }

        for (int i = n - 1; i >= 0; --i) {

            int digit = (a[i] / exponent) % 10;

            --count[digit];

            output[count[digit]] = a[i];
        }

        for (int i = 0; i < n; ++i) {
            a[i] = output[i];
        }

    }

}
