/*
 * Matrix-chain multiplication (CLRS interval dynamic programming).
 *
 * Matrix i has dimensions dimensions[i] by dimensions[i + 1].  The caller
 * supplies matrix_count * matrix_count integers in cost as the DP workspace.
 * The verified interface bounds matrix_count and the dimensions so that every
 * scalar-multiplication count below fits in a signed 32-bit int.
 */

int matrixChainMinCost(int *dimensions, int matrix_count, int *cost)

{
  int width = matrix_count;

  /* A one-matrix product needs no scalar multiplications.  Clearing the whole
   * table also gives defined values to the caller's complete workspace. */

  for (int i = 0; i < matrix_count * width; ++i) {
    cost[i] = 0;
  }

  /* After finishing a chain length, every shorter interval already contains
   * its minimum cost, so it is available to each candidate split below. */

  for (int chain_length = 2;
       chain_length <= matrix_count;
       ++chain_length) {

    for (int left = 0;
         left + chain_length <= matrix_count;
         ++left) {
      int right = left + chain_length - 1;

      /* Use the leftmost split as a real initial candidate. */

      int best = cost[left * width + left]
               + cost[(left + 1) * width + right]
               + dimensions[left] * dimensions[left + 1]
               * dimensions[right + 1];

      for (int split = left + 1; split < right; ++split) {

        int candidate = cost[left * width + split]
                      + cost[(split + 1) * width + right]
                      + dimensions[left] * dimensions[split + 1]
                      * dimensions[right + 1];

        if (candidate < best) {
          best = candidate;
        }
      }

      cost[left * width + right] = best;
    }
  }

  return cost[matrix_count - 1];
}
