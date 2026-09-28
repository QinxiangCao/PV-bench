/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (RodCutOptimalRevenue : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.rod_cutting.rocq.spec_lib */

int rod_cutting(const int *price, int n)
/*@ With (price_l : list Z)
    Require
      0 <= n && n <= 1000 &&
      Zlength(price_l) == n + 1 &&
      price_l[0] == 0 &&
      Forall(Z::le(0), price_l) && Forall(Z::ge(1000000), price_l) &&
      IntArray::full(price, n + 1, price_l)
    Ensure
      RodCutOptimalRevenue(price_l, n, __return) &&
      IntArray::full(price, n + 1, price_l)
 */
{
  int revenue[1001];

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

    int result = revenue[n];
    
  return result;
}
