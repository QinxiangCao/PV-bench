/*@ Extern Coq
      (Power2 : Z -> Z)
      (RangeMaxValue : list Z -> Z -> Z -> Z -> Prop)
      (STBuilt : list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.rmq.rocq.spec_lib */

void build(int *arr, int n, int K, int *st)

{

  for (int idx = 0; idx < n * K; ++idx) {
    st[idx] = 0;
  }

  for (int i = 0; i < n; ++i) {

    st[i * K] = arr[i];
  }

  int half = 1;
  int len = 2;

  for (int j = 1; j < K; ++j) {

    for (int i = 0; i + len <= n; ++i) {

      int a = st[i * K + j - 1];
      int b = st[(i + half) * K + j - 1];
      if (a >= b) {
        st[i * K + j] = a;
      } else {
        st[i * K + j] = b;
      }
    }
    half = len;
    len = len * 2;
  }
}

int query(int *st, int n, int K, int left, int right)
/*@ With (l : list Z) (st_l : list Z)
    Require
      1 <= n && n <= 100000 && 1 <= K && K <= 30 &&
      n * K <= 1000000 && n < Power2(K) &&
      0 <= left && left <= right && right < n &&
      Zlength(l) == n && STBuilt(l, st_l, K, n) &&
      IntArray::full(st, n * K, st_l)
    Ensure
      RangeMaxValue(l, left, right + 1, __return) &&
      IntArray::full(st, n * K, st_l)
 */
{
  int len = right - left + 1;
  int k = 0;
  int pow = 1;

  while (pow * 2 <= len) {
    pow = pow * 2;
    k++;
  }

  int a = st[left * K + k];
  int b = st[(right - pow + 1) * K + k];
  if (a >= b) {
    return a;
  } else {
    return b;
  }
}
