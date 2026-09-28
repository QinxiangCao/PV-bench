/*@ Extern Coq
      (PrimeForLinearInverse : Z -> Prop)
      (ModularInversePrefix : Z -> Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.linear_modular_inverse.rocq.spec_lib */

void linear_modular_inverse(int p, int *inverse)
/*@ Require
      PrimeForLinearInverse(p) &&
      2 <= p && p <= 46340 &&
      IntArray::undef_seg(inverse, 1, p)
    Ensure
      exists values,
      ModularInversePrefix(p, p, values) &&
      IntArray::seg(inverse, 1, p, values)
 */
{
    inverse[1] = 1;

    for (int i = 2; i < p; ++i) {
        int quotient = p / i;
        int remainder = p % i;
        
        inverse[i] = ((p - quotient) * inverse[remainder]) % p;
    }
}
