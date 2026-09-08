/*@ Import Lean
import Algorithms.optimized_selection_sort.lean.spec_lib
open scoped SimpleC
*/
/*@ Extern Coq
      (optimized_selection_sort_result : list Z -> list Z -> Prop)
 */

void optimized_selection_sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(input) == n &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        optimized_selection_sort_result(input, output) &&
        Permutation(input, output) &&
        increasing(output) &&
        Zlength(output) == n &&
        IntArray::full(a, n, output)
 */
{
    int i;

    for (i = 0; i + 1 < n; ++i) {
        int min_index = i;
        int j;

        for (j = i + 1; j < n; ++j) {
            if (a[j] < a[min_index]) {
                min_index = j;
            }
        }

        /* Avoid the three writes when the current element is already minimal. */
        if (min_index != i) {
            int tmp = a[i];
            a[i] = a[min_index];
            a[min_index] = tmp;
        }
    }
}
