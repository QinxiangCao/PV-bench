/*@ Import Lean
import Algorithms.huffman_encoding.lean.spec_lib
open scoped SimpleC
*/

/*
 * Huffman encoding: minimum weighted path length of a binary prefix code.
 *
 * Repeatedly merging the two smallest live weights constructs a Huffman tree.
 * The sum of all merge weights is that tree's weighted path length and is
 * minimum among all full binary prefix-code trees over the input frequencies.
 *
 * This verification-oriented implementation uses a fresh selection scan for
 * each of the two minima.  Removing a selected item is done by moving the last
 * live item into its slot, so only the prefix work[0..active) is live.
 */

/*@ Extern Coq
      (HuffmanInputBounded : list Z -> Prop)
      (HuffmanOptimalCost : list Z -> Z -> Prop)
      (HuffmanScratchFinal : list Z -> list Z -> Prop)
 */
int huffman_cost(int *weights, int n, int *work)
/*@ With (weights_l : list Z)
    Require
      1 <= n && n <= 8 &&
      Zlength(weights_l) == n &&
      HuffmanInputBounded(weights_l) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::undef_full(work, n)
    Ensure
      exists work_l,
        Zlength(work_l) == n &&
        HuffmanOptimalCost(weights_l, __return) &&
        HuffmanScratchFinal(weights_l, work_l) &&
        0 <= __return && __return <= 56000 &&
        IntArray::full(weights, n, weights_l) *
        IntArray::full(work, n, work_l)
 */
{

  for (int i = 0; i < n; ++i) {
    work[i] = weights[i];
  }

  int active = n;
  int total = 0;

  while (active > 1) {
    int first = 0;

    for (int i = 1; i < active; ++i) {

      if (work[i] < work[first]) {
        first = i;
      }
    }

    int x = work[first];
    --active;

    work[first] = work[active];

    int second = 0;

    for (int i = 1; i < active; ++i) {
      if (work[i] < work[second]) {
        second = i;
      }
    }

    int y = work[second];
    --active;

    work[second] = work[active];

    int merged = x + y;
    total += merged;
    work[active] = merged;
    ++active;
  }

  return total;
}
