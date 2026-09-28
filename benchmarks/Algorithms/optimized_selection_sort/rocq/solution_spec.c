/*@ Extern Coq
      (optimized_selection_sort_result : list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.optimized_selection_sort.rocq.spec_lib */

void optimized_selection_sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(input) == n &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        optimized_selection_sort_result(input, output) &&
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

        if (min_index != i) {
            int tmp = a[i];
            a[i] = a[min_index];
            a[min_index] = tmp;
        }
    }
}
