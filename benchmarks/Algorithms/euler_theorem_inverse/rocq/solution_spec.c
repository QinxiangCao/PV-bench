/*@ Extern Coq
      (Zgcd : Z -> Z -> Z)
      (EulerTheoremInverse : Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.euler_theorem_inverse.rocq.spec_lib */

int euler_phi(int value)

{
    int result = value;

    for (int factor = 2; factor * factor <= value; ++factor) {
        if (value % factor == 0) {
            
            while (value % factor == 0) {
                value /= factor;
            }

            result = result / factor * (factor - 1);
        }
    }

    if (value != 1) {
        result = result / value * (value - 1);
    }

    return result;
}

int modular_power(int base, int exponent, int modulus)

{
    int result = 1;

    while (exponent > 0) {
        if (exponent % 2 == 1) {
            result = result * base % modulus;
        }
        base = base * base % modulus;
        exponent /= 2;
    }

    return result;
}

int euler_theorem_inverse(int value, int modulus)
/*@ Require
      0 < value && value < modulus &&
      2 <= modulus && modulus <= 46341 &&
      Zgcd(value, modulus) == 1 && emp
    Ensure
      0 <= __return && __return < modulus &&
      EulerTheoremInverse(value, modulus, __return) && emp
 */
{
    int exponent = euler_phi(modulus) - 1;

    return modular_power(value, exponent, modulus);
}
