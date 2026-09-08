int check(int *arr, int n, int m, int cap)

{
  int cnt = 1;
  int cur = 0;

  for (int i = 0; i < n; ++i) {
    int x = arr[i];
    if (x > cap) {
      return 0;
    }
    if (cur + x > cap) {
      cnt = cnt + 1;
      cur = x;
    } else {
      cur = cur + x;
    }
  }
  if (cnt <= m) {
    return 1;
  } else {
    return 0;
  }
}

int splitArrayLargestSum(int *arr, int n, int m)

{
  int left = 0;
  int right = 1000000000;

  while (left < right) {
    int mid = left + (right - left) / 2;
    int ok = check(arr, n, m, mid);
    if (ok) {
      right = mid;
    } else {
      left = mid + 1;
    }
  }

  return left;
}
