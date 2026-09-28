/*@ Extern Coq
      (ModularPower : Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.modular_power.rocq.spec_lib */

int modular_power(int a, int b, int modulus)
/*@ Require
      0 <= a && a < modulus &&
      0 <= b &&
      2 <= modulus && modulus <= 100000 && emp
    Ensure
      ModularPower(a, b, modulus, __return) && emp
 */
{
    int result = 1;

    while (b > 0) {
        if (b % 2 == 1) {
            result = (int)((long long)result * a % modulus);
        }
        a = (int)((long long)a * a % modulus);
        b /= 2;
    }

    return result;
}
