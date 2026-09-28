int huffman_cost(int *weights, int n)

{
  int work[8];

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
