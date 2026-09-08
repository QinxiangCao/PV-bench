int paint_house_ii(int **costs, int n, int k)

{
  int min1 = 0;
  int min2 = 0;
  int min1_color = -1;

  for (int i = 0; i < n; ++i) {
    int new_min1 = 1000000000;
    int new_min2 = 1000000000;
    int new_min1_color = -1;

    for (int c = 0; c < k; ++c) {
      int prev;
      if (c == min1_color) {
        prev = min2;
      } else {
        prev = min1;
      }

      int total = prev + costs[i][c];

      if (total < new_min1) {
        new_min2 = new_min1;
        new_min1 = total;
        new_min1_color = c;
      } else {
        if (total < new_min2) {
          new_min2 = total;
        }
      }

    }

    min1 = new_min1;
    min2 = new_min2;
    min1_color = new_min1_color;

  }

  return min1;
}
