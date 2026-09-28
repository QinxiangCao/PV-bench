int matrixChainMinCost(int *dimensions, int matrix_count)

{
  int cost[64];

  int width = matrix_count;

  for (int i = 0; i < matrix_count * width; ++i) {
    cost[i] = 0;
  }

  for (int chain_length = 2;
       chain_length <= matrix_count;
       ++chain_length) {

    for (int left = 0;
         left + chain_length <= matrix_count;
         ++left) {
      int right = left + chain_length - 1;

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

  int result = cost[matrix_count - 1];

  return result;
}
