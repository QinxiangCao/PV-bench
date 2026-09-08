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

int huffman_cost(int *weights, int n, int *work)

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
