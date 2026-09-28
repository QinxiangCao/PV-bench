/*@ Extern Coq
      (Modern::PrimePrefixList : Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.sieve_of_euler.rocq.spec_lib */

int *get_prime(int n, int tot, int *prime)
/*@ With (prime0 : list Z)
    Require
      2 <= n && n <= 46340 &&
      Zlength(prime0) == n &&
      IntArray::seg(prime, 1, n + 1, prime0)
    Ensure
      exists prime_out final_tot,
      __return == prime@pre &&
      0 <= final_tot && final_tot <= n@pre &&
      Modern::PrimePrefixList(n@pre, final_tot, prime_out) &&
      IntArray::seg(prime@pre, 1, n@pre + 1, prime_out)
 */
{
     int flag[46341];

     for (int z = 2; z <= n; ++z) {
          flag[z] = 0;
     }

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
