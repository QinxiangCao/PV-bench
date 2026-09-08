/*@ Import Lean
import Algorithms.modular_power.lean.spec_lib
open scoped SimpleC
*/
/*@ Extern Coq
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
 */

int modular_power(int a, int b, int modulus)
/*@ Require
      0 <= a && a < modulus &&
      0 <= b &&
      2 <= modulus && modulus <= 46341 && emp
    Ensure
      0 <= __return && __return < modulus &&
      ModularPower(a, b, modulus, __return) && emp
 */
{
    int result = 1;

    while (b > 0) {
        if (b % 2 == 1) {
            result = result * a % modulus;
        }
        a = a * a % modulus;
        b /= 2;
    }

    return result;
}
