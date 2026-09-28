void swap_ministers(int *a, int n, int i, int j)

{
  int tmp_left = a[2 * i];
  int tmp_right = a[2 * i + 1];
  a[2 * i] = a[2 * j];
  a[2 * i + 1] = a[2 * j + 1];
  a[2 * j] = tmp_left;
  a[2 * j + 1] = tmp_right;
}

void kings_game(int *ministers, int n, int king_left, int king_right, int *ans)

{
  (void)king_right;

  for (int k = 0; k < 2 * n; k++) {
    ans[k] = ministers[k];
  }

  for (int pass = 0; pass < n - 1; pass++) {

    for (int j = 0; j < n - 1 - pass; j++) {
      int left1 = ans[2 * j];
      int right1 = ans[2 * j + 1];
      int left2 = ans[2 * (j + 1)];
      int right2 = ans[2 * (j + 1) + 1];

      if (left1 * right1 > left2 * right2) {
        swap_ministers(ans, n, j, j + 1)  ;
      }
    }
  }
}
