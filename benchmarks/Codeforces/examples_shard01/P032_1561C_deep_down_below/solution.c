/*
 * Codeforces 1561/C - Deep Down Below  (rating 1300, GREEDY)
 *
 * Cave i can only be entered with power at least req_i = max_j (a_ij + 1 - j)
 * (j counted from 0, since j monsters were already beaten inside), and leaving
 * it adds k_i power.  Clearing caves in increasing order of req is optimal, so
 * the answer is max_i (req_i - power already gained before cave i).
 */

#include <stdio.h>

/* Sort the two parallel arrays by requirement. */
static void sift_caves(long long *req, long long *gain, int root, int hi)
{
    while (2 * root + 1 <= hi) {
        int child = 2 * root + 1;
        if (child + 1 <= hi && req[child] < req[child + 1])
            child++;
        if (req[root] >= req[child])
            return;
        long long t = req[root]; req[root] = req[child]; req[child] = t;
        t = gain[root]; gain[root] = gain[child]; gain[child] = t;
        root = child;
    }
}

static void sort_caves(long long *req, long long *gain, int n)
{
    for (int root = n / 2 - 1; root >= 0; root--) {
        sift_caves(req, gain, root, n - 1);
    }
    for (int hi = n - 1; hi > 0; hi--) {
        long long t = req[0]; req[0] = req[hi]; req[hi] = t;
        t = gain[0]; gain[0] = gain[hi]; gain[hi] = t;
        sift_caves(req, gain, 0, hi - 1);
    }
}

/* solver: minimum starting power.  Sorts req[]/gain[] together. */
static long long solver(long long *req, long long *gain, int n)
{
    sort_caves(req, gain, n);
    long long need = 0, gained = 0;
    for (int i = 0; i < n; i++) {
        long long start = req[i] - gained;
        if (start > need)
            need = start;
        gained += gain[i];
    }
    return need;
}

int main(void)
{
    int t;
    if (scanf("%d", &t) != 1)
        return 0;
    static long long reqs[100005], gains[100005];
    while (t--) {
        int n;
        scanf("%d", &n);
        for (int i = 0; i < n; i++) {
            int k;
            scanf("%d", &k);
            long long req = 0;
            for (int j = 0; j < k; j++) {
                long long a;
                scanf("%lld", &a);
                long long r = a + 1 - j;
                if (r > req)
                    req = r;
            }
            reqs[i] = req;
            gains[i] = k;
        }
        printf("%lld\n", solver(reqs, gains, n));
    }
    return 0;
}
