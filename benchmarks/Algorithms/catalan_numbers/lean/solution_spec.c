/*@ Import Lean
import Algorithms.catalan_numbers.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (StackSequenceCount : Z -> Z -> Prop)
      (StackRowsDone : Z -> list Z -> Z -> Prop)
 */

int id(int n, int x, int y)

{
    return x * (n + 1)  + y;
}

int solve(int n, int *f)
/*@ Require
      0 <= n && n <= 7 &&
      IntArray::undef_full(f, (n + 1) * (n + 1))
    Ensure
      exists table,
      StackSequenceCount(n, __return) &&
      StackRowsDone(n, table, n + 1) &&
      IntArray::full(f, (n + 1) * (n + 1), table)
 */
{

    for (int i = 0; i <= n; i++) {

        for (int j = 0; j <= n; j++) {
            if (i == 0) {
                f[id(n, i, j)] = 1;
            }
            else if (j == 0) {

                f[id(n, i, j)] = f[id(n, i-1, j+1)];
            }
            else {

                f[id(n, i, j)] = f[id(n, i-1, j+1)] + f[id(n, i, j-1)];
            }

        }

    }

    return f[id(n, n, 0)];
}
