/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
 */
/*@ Extern Coq
      (increasing : list Z -> Prop)
 */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.bucket_sort.rocq.spec_lib */

void sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= 1000 &&
      Forall(Z::le(0), input) && Forall(Z::ge(999999999), input) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        Permutation(input, output) && increasing(output) &&
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
