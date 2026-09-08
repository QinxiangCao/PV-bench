/*@ Extern Coq
      (PrimeIndicatorList : Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.sieve_of_eratosthenes.rocq.spec_lib */

void solve(int n, int *f)
/*@ With (initial : list Z)
    Require
      2 <= n && n <= 1000000000 &&
      Zlength(initial) == n &&
      IntArray::seg(f, 1, n + 1, initial)
    Ensure
      exists result,
      PrimeIndicatorList(n, result) &&
      IntArray::seg(f, 1, n + 1, result)
 */
{

    for (int i = 1; i <= n; i++) {
        f[i] = 1;
    }
    f[1] = 0;
    f[2] = 1;

    for (int i = 2; i <= n; i++) {
        if (f[i] == 1) {

            for (int j = i * 2; j <= n; j = j + i) {
                f[j] = 0;
            }

        }

    }

}
