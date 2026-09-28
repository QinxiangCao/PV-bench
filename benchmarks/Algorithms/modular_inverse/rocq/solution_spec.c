/*@ Extern Coq
      (ModularInverse : Z -> Z -> Z -> Prop)
 */
/*@ Extern Coq (Zgcd : Z -> Z -> Z) */
/*@ Import Coq Require Import PVbench.Algorithms.modular_inverse.rocq.spec_lib */

int exgcd(int a, int b, int *x, int *y)
;

int modular_inverse(int a, int modulus)
/*@ Require
      1 < modulus && 0 < a && a < modulus && Zgcd(a, modulus) == 1 && emp
    Ensure
      0 <= __return && __return < modulus &&
      ModularInverse(a, modulus, __return) && emp
*/
{
    int x;
    int y;
    int g = exgcd(a, modulus, &x, &y);

    int inverse = x % modulus;
    if (inverse < 0) {
        inverse += modulus;
    }
    return inverse;
}
