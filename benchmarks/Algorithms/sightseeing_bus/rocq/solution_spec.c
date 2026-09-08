/*@ Extern Coq
      (SightseeingInputsBounded : Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (DestinationCounts : Z -> Z -> list Z -> list Z -> Prop)
      (SightseeingOptimalState : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.sightseeing_bus.rocq.spec_lib */

int solve(int n, int m, int k, int *d, int *t, int *a, int *b,
          int *late, int *off, int *arr)
/*@ With (dist times origins destinations : list Z)
    Require
      0 <= k && k <= 100000 &&
      SightseeingInputsBounded(n, m, dist, times, origins, destinations) &&
      IntArray::full(d, n - 1, dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations) *
      IntArray::undef_full(late, n) *
      IntArray::undef_full(off, n) *
      IntArray::undef_full(arr, n)
    Ensure
      exists final_dist latest counts arrivals,
      SightseeingOptimalState(
        n, m, k@pre, dist, times, origins, destinations,
        final_dist, latest, arrivals, __return) &&
      DestinationCounts(n, m, destinations, counts) &&
      IntArray::full(d, n - 1, final_dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations) *
      IntArray::full(late, n, latest) *
      IntArray::full(off, n, counts) *
      IntArray::full(arr, n, arrivals)
*/
{
    int i;
    int j;
    int cur;
    int best;
    int pos;
    int cnt;
    int ans;

    for (i = 0; i < n; ++i) {
        late[i] = 0;
        off[i] = 0;
    }

    for (i = 0; i < m; ++i) {
        int x = a[i] - 1;
        int y = b[i] - 1;

        if (late[x] < t[i]) {
            late[x] = t[i];
        }
        off[y] = off[y] + 1;
    }

    cur = 0;

    for (i = 0; i < n; ++i) {
        arr[i] = cur;
        if (cur < late[i]) {
            cur = late[i];
        }
        if (i + 1 < n) {
            cur = cur + d[i];
        }
    }

    while (k > 0) {
        best = 0;
        pos = -1;

        for (i = 0; i + 1 < n; ++i) {
            if (d[i] > 0) {
                cnt = 0;

                for (j = i + 1; j < n; ++j) {
                    cnt = cnt + off[j];
                    if (arr[j] <= late[j]) {
                        break;
                    }
                }

                if (best < cnt) {
                    best = cnt;
                    pos = i;
                }
            }
        }

        if (pos < 0 || best == 0) {
            break;
        }
        d[pos] = d[pos] - 1;

        for (i = pos + 1; i < n; ++i) {
            arr[i] = arr[i] - 1;
            if (arr[i] < late[i]) {
                break;
            }
        }

        k = k - 1;
    }

    ans = 0;

    for (i = 0; i < m; ++i) {

        ans = ans + arr[b[i] - 1] - t[i];
    }
    return ans;
}
