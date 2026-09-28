/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::lt : Z -> Z -> Prop)
      (SightseeingMinimumTotal : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.sightseeing_bus.rocq.spec_lib */

int solve(int n, int m, int k, int *d, int *t, int *a, int *b)
/*@ With (dist times origins destinations : list Z)
    Require
      0 <= k && k <= 100000 &&
      2 <= n && n <= 1000 &&
        1 <= m && m <= 10000 &&
        Zlength(dist) == n - 1 &&
        Zlength(times) == m && Zlength(origins) == m &&
        Zlength(destinations) == m &&
        Forall(Z::le(0), dist) && Forall(Z::ge(100), dist) &&
        Forall(Z::le(0), times) && Forall(Z::ge(100000), times) &&
        Forall(Z::le(1), origins) && Forall(Z::ge(n), destinations) &&
        Forall2(Z::lt, origins, destinations) &&
      IntArray::full(d, n - 1, dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations)
    Ensure
      exists final_dist,
      SightseeingMinimumTotal(n, m, k@pre, dist, times, origins, destinations, __return) &&
      IntArray::full(d, n - 1, final_dist) *
      IntArray::full(t, m, times) *
      IntArray::full(a, m, origins) *
      IntArray::full(b, m, destinations)
*/
{
    int late[1000];
    int off[1000];
    int arr[1000];

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
