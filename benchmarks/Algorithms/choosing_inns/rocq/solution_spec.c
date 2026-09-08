/*@ Extern Coq
      (ChoosingInputSafe : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (ChoosingInnsAnswer : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
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
    int *colors, int *costs, int n, int k, int p,
    int *seen, int *good)
/*@ With (colors_l : list Z) (costs_l : list Z)
    Require
      ChoosingInputSafe(colors_l, costs_l, n, k, p) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l) *
      IntArray::undef_full(seen, k) *
      IntArray::undef_full(good, k)
    Ensure
      exists seen_l good_l,
      ChoosingInnsAnswer(colors_l, costs_l, n, k, p, __return) &&
      0 <= __return && __return <= 19999900000 &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l) *
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_l)
 */
{
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
