/*@ Extern Coq
      (EulerSieveResult : Z -> Z -> list Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.sieve_of_euler.rocq.spec_lib */

int *get_prime(int n, int tot, int *flag, int *prime)
/*@ With (flag0 : list Z) (prime0 : list Z)
    Require
      2 <= n && n <= 46340 &&
      Zlength(flag0) == n - 1 &&
      Zlength(prime0) == n &&
      IntArray::seg(flag, 2, n + 1, flag0) *
      IntArray::seg(prime, 1, n + 1, prime0)
    Ensure
      exists flag_out prime_out final_tot,
      __return == prime@pre &&
      EulerSieveResult(n@pre, final_tot, flag_out, prime_out) &&
      IntArray::seg(flag@pre, 2, n@pre + 1, flag_out) *
      IntArray::seg(prime@pre, 1, n@pre + 1, prime_out)
 */
{
	tot = 0;

     for (int i = 2; i <= n; i++)
		flag[i] = i;

	for (int i = 2; i <= n; i++) {
		if (flag[i] == i) {
               tot = tot + 1;
               prime[tot] = i;
          }

		for (int j = 1; i * prime[j] <= n && j <= tot; j++) {
			flag[i * prime[j]] = prime[j];

			if (i % prime[j] == 0) {

                    break;
               }

		}

	}

     return prime;
}
