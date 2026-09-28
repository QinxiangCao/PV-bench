/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
 */
/*@ Extern Coq
      (increasing : list Z -> Prop)
 */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::gt : Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.counting_sort.rocq.spec_lib */

void sort(int *a, int n)
/*@ With (input : list Z)
    Require
      0 <= n && n <= 100 &&
      Zlength(input) == n &&
      Forall(Z::le(0), input) && Forall(Z::gt(100), input) &&
      IntArray::full(a, n, input)
    Ensure
      exists output,
        Permutation(input, output) &&
        increasing(output) &&
        IntArray::full(a, n, output)
 */
{
    int count[100];
    int output[100];

    for (int value = 0; value < 100; ++value) {
        count[value] = 0;
    }

    for (int i = 0; i < n; ++i) {

        ++count[a[i]];
    }

    for (int value = 1; value < 100; ++value) {
        count[value] += count[value - 1];
    }

    for (int i = n - 1; i >= 0; --i) {

        int value = a[i];

        --count[value];

        output[count[value]] = value;
    }

    for (int i = 0; i < n; ++i) {
        a[i] = output[i];
    }

}
