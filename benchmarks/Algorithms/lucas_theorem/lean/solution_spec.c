/*@ Import Lean
import Algorithms.lucas_theorem.lean.spec_lib
open scoped SimpleC
*/

/*
 * Compute C(n + m, n) modulo a prime p with Lucas' theorem.
 *
 * The problem guarantees
 *
 *   1 <= n, m, p <= 100000
 *
 * and that p is prime.  For this verification example, all arithmetic used by
 * the program is additionally assumed to stay within the signed int range.
 *
 * Input/output handling is intentionally left to the caller.  The function
 * lucas_theorem is the algorithmic entry point for one test case.
 */

/*@ Extern Coq
      (PrimeForLucas : Z -> Prop)
      (LucasMachineSafe : Z -> Z -> Z -> Prop)
      (LucasBinomialResidue : Z -> Z -> Z -> Z -> Prop)
 */


int modular_power(int base, int exponent, int modulus)
;

/*
 * Compute C(upper, lower) modulo prime, where
 * 0 <= lower <= upper < prime.
 *
 * Because every factor in lower! is nonzero modulo prime, Fermat's little
 * theorem gives lower!^(prime - 2) as its modular inverse.
 */
int binomial_digit_mod_prime(int upper, int lower, int prime)

{
    if (lower > upper) {
        return 0;
    }

    if (lower > upper - lower) {
        lower = upper - lower;
    }

    int numerator = 1;
    int denominator = 1;

    for (int i = 1; i <= lower; ++i) {
        int factor = upper - lower + i;
        int numerator_product = numerator * factor;
        int denominator_product = denominator * i;

        numerator = numerator_product % prime;
        denominator = denominator_product % prime;
    }

    int inverse = modular_power(denominator, prime - 2, prime);
    int answer = numerator * inverse;
    return answer % prime;
}

int lucas_theorem(int n, int m, int prime)
/*@ Require
      1 <= n && n <= 100000 &&
      1 <= m && m <= 100000 &&
      2 <= prime && prime <= 100000 &&
      PrimeForLucas(prime) &&
      LucasMachineSafe(n, m, prime) && emp
    Ensure
      0 <= __return && __return < prime@pre &&
      LucasBinomialResidue(n@pre, m@pre, prime@pre, __return) && emp
 */
{
    int upper = n + m;
    int lower = n;
    int result = 1;

    while (upper > 0 || lower > 0) {
        int upper_digit = upper % prime;
        int lower_digit = lower % prime;

        if (lower_digit > upper_digit) {
            return 0;
        }

        int digit_binomial =
            binomial_digit_mod_prime(upper_digit, lower_digit, prime);
        int product = result * digit_binomial;
        result = product % prime;

        upper /= prime;
        lower /= prime;
    }

    return result;
}
