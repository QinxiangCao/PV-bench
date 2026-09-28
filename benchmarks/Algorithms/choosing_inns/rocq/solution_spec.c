/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (InnsPairAnswer : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.choosing_inns.rocq.spec_lib */

void initCounts(int *seen, int *good, int k)

{

  for (int i = 0; i < k; ++i) {
    seen[i] = 0;
    good[i] = 0;

  }
}

void copyCounts(int *seen, int *good, int k)

{

  for (int i = 0; i < k; ++i) {
    good[i] = seen[i];

  }
}

long long countChoosingInns(
    int *colors, int *costs, int n, int k, int p)
/*@ With (colors_l : list Z) (costs_l : list Z)
    Require
      0 <= n && n <= 200000 && 1 <= k && k <= 50 && 0 <= p && p <= 100 && Zlength(colors_l) == n && Zlength(costs_l) == n && Forall(Z::le(0), colors_l) && Forall(Z::ge(k - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l)
    Ensure
      InnsPairAnswer(colors_l, costs_l, n, p, __return) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l)
 */
{
  int seen[50];
  int good[50];
  long long answer = 0;

  initCounts(seen, good, k);

  for (int i = 0; i < n; ++i) {
    {
      int c = colors[i];
      int cost = costs[i];

      if (cost <= p) {
        answer = answer + seen[c];
        seen[c] = seen[c] + 1;

        copyCounts(seen, good, k);

      } else {
        answer = answer + good[c];
        seen[c] = seen[c] + 1;

      }
    }
  }

  return answer;
}
