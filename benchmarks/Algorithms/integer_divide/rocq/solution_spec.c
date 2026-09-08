/*@ Extern Coq
      (PrimeFactorization : Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.integer_divide.rocq.spec_lib */

void divide(int n, int *p)
/*@ With (original : Z)
    Require
      n == original &&
      1 <= original && original <= INT_MAX &&
      IntArray::undef_full(p, original)
    Ensure
      exists factors,
      PrimeFactorization(original, factors) &&
      Zlength(factors) < original &&
      IntArray::undef_seg(p, 0, 1) *
      IntArray::seg(p, 1, 1 + Zlength(factors), factors) *
      IntArray::undef_seg(p, 1 + Zlength(factors), original)
 */
{
	int cnt = 0;

	for (int i = 2; i <= n; i++) {

		while (n % i == 0) {

			cnt++;
			p[cnt] = i;
			n /= i;
		}
		if (n == 1) {
			break;
		}

	}
}
