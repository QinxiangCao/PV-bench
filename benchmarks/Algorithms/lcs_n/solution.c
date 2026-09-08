int lcs_n(int *x, int *y, int n, int *table)

{
  int stride;
  int i;
  int j;
  int above;
  int left;

  stride = n + 1;

  i = 0;

  while (i <= n) {

    table[stride * i] = 0;
    i = i + 1;
  }

  j = 1;

  while (j <= n) {

    table[j] = 0;
    j = j + 1;
  }

  i = 1;

  while (i <= n) {
    j = 1;

    while (j <= n) {

      if (x[i - 1] == y[j - 1]) {

        table[stride * i + j] =
            table[stride * (i - 1) + (j - 1)] + 1;
      } else {

        above = table[stride * (i - 1) + j];
        left = table[stride * i + (j - 1)];
        if (above >= left) {
          table[stride * i + j] = above;
        } else {
          table[stride * i + j] = left;
        }
      }

      j = j + 1;
    }
    i = i + 1;
  }

  return table[stride * n + n];
}
