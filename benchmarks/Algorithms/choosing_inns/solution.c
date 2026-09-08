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
