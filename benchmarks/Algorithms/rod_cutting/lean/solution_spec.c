/*@ Import Lean
import Algorithms.rod_cutting.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (RodCutRevenueTable : list Z -> list Z -> Z -> Prop)
 */
int rod_cutting(const int *price, int *revenue, int n)
/*@ With (price_l : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(price_l) == n + 1 &&
      price_l[0] == 0 &&
      (forall (k : Z),
        (0 <= k && k <= n) => (0 <= price_l[k] && price_l[k] <= 1000000)) &&
      IntArray::full(price, n + 1, price_l) *
      IntArray::undef_full(revenue, n + 1)
    Ensure
      exists revenue_l,
      Zlength(revenue_l) == n + 1 &&
      RodCutRevenueTable(price_l, revenue_l, n + 1) &&
      __return == revenue_l[n] &&
      (forall (k : Z),
        (0 <= k && k < n + 1) =>
          (0 <= revenue_l[k] && revenue_l[k] <= k * 1000000)) &&
      IntArray::full(price, n + 1, price_l) *
      IntArray::full(revenue, n + 1, revenue_l)
 */
{
    int j;

    revenue[0] = 0;

    for (j = 1; j <= n; ++j) {
        int best = 0;
        int i;

        for (i = 1; i <= j; ++i) {

            int candidate = price[i] + revenue[j - i];
            if (best < candidate) {
                best = candidate;
            }
        }
        revenue[j] = best;
    }

    return revenue[n];
}
