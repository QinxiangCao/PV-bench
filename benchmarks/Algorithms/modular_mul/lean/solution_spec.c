/*@ Import Lean
import Algorithms.modular_mul.lean.spec_lib
open scoped SimpleC
*/
/*@ Extern Coq
      (ModularMul : Z -> Z -> Z -> Z -> Prop)
 */

int modular_mul(int a, int b, int modulus)
/*@ Require
      0 - modulus < a && a < modulus &&
      INT_MIN < b && b <= INT_MAX &&
      0 < modulus && modulus * 2 <= INT_MAX && emp
    Ensure
      ModularMul(a, b, modulus, __return) && emp
*/
{
    int res = 0;
    int flag = 1;
    if (b < 0) {
        b = -b;
        flag = -1;
    }

    while (b > 0) {
        if (b % 2 == 1) {
            res = (res + a) % modulus;
        }
        b = b / 2;
        a = (a + a) % modulus;
    }
    return res * flag;
}
