/*@ Import Lean
import Codeforces.examples_shard01.P086_639D_bear_and_contribution.lean.spec_lib
open scoped SimpleC
*/
/*
 * Codeforces 639/D - Bear and Contribution  (rating 2400, GREEDY)
 *
 * Raising a user by d costs (d mod 5)*c + (d/5)*min(b, 5c): the remainder must
 * come from comments, and each further block of five is a blog or five
 * comments, whichever is cheaper.  Fix the target's residue mod 5 and sweep
 * the targets upward; every eligible user then costs base_i + (x/5)*W with a
 * fixed base, so a size-k max-heap of the smallest bases gives the best k.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Z -> list Z -> Z -> Prop)
*/

#define SHIFT 2000000000LL

static void hpush(long long *heap, int *hsize, long long *hsum, long long v)
{
    int i = *hsize;
    *hsize = *hsize + 1;
    heap[i] = v;
    *hsum += v;
    while (i > 0) {                       /* max-heap */
        int p = (i - 1) / 2;
        if (heap[p] >= heap[i])
            break;
        long long t = heap[p]; heap[p] = heap[i]; heap[i] = t;
        i = p;
    }
}

static void hpop(long long *heap, int *hsize, long long *hsum)
{
    *hsum -= heap[0];
    *hsize = *hsize - 1;
    heap[0] = heap[*hsize];
    int i = 0;
    while (1) {                           /* max-heap */
        int l = 2 * i + 1, r = l + 1, big = i;
        if (l < *hsize && heap[l] > heap[big]) big = l;
        if (r < *hsize && heap[r] > heap[big]) big = r;
        if (big == i)
            break;
        long long t = heap[big]; heap[big] = heap[i]; heap[i] = t;
        i = big;
    }
}

static void sift_candidates(long long *cand_t, long long *cand_base,
                            int root, int hi)
{
    while (2 * root + 1 <= hi) {
        int child = 2 * root + 1;
        if (child + 1 <= hi && cand_t[child] < cand_t[child + 1])
            child++;
        if (cand_t[root] >= cand_t[child])
            return;
        long long v = cand_t[root]; cand_t[root] = cand_t[child];
        cand_t[child] = v;
        v = cand_base[root]; cand_base[root] = cand_base[child];
        cand_base[child] = v;
        root = child;
    }
}

static void sort_candidates(long long *cand_t, long long *cand_base, int n)
{
    for (int root = n / 2 - 1; root >= 0; root--)
        sift_candidates(cand_t, cand_base, root, n - 1);
    for (int hi = n - 1; hi > 0; hi--) {
        long long v = cand_t[0]; cand_t[0] = cand_t[hi]; cand_t[hi] = v;
        v = cand_base[0]; cand_base[0] = cand_base[hi]; cand_base[hi] = v;
        sift_candidates(cand_t, cand_base, 0, hi - 1);
    }
}

/* solver: minimum minutes so that k users share a contribution. */
static long long solver(const long long *values, int n, int k, long long b,
                        long long c, long long *shifted,
                        long long *cand_t, long long *cand_base,
                        long long *heap)
/*@ With (contributions : list Z)
    Require
      2 <= k && k <= Zlength(contributions) && 1 <= b && b <= 1000 && 1 <= c && c <= 1000 &&
      k <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (-1000000000 <= contributions[i] && contributions[i] <= 1000000000)) && n == Zlength(contributions) && Int64Array::full(values, n, contributions) * Int64Array::full_shape(shifted, n) * Int64Array::full_shape(cand_t, n) * Int64Array::full_shape(cand_base, n) * Int64Array::full_shape(heap, n)
    Ensure
      Spec(k, b, c, contributions, __return) && Int64Array::full(values, n, contributions) * Int64Array::full_shape(shifted, n) * Int64Array::full_shape(cand_t, n) * Int64Array::full_shape(cand_base, n) * Int64Array::full_shape(heap, n)
*/
{
    long long W = b < 5 * c ? b : 5 * c;
    long long best = -1;
    for (int i = 0; i < n; i++)
        shifted[i] = values[i] + SHIFT;
    for (int j = 0; j < 5; j++) {
        for (int i = 0; i < n; i++) {
            long long rem = ((j - shifted[i]) % 5 + 5) % 5;
            long long tp = shifted[i] + rem; /* raised to target residue */
            cand_t[i] = tp;
            cand_base[i] = rem * c - (tp - j) / 5 * W;
        }
        sort_candidates(cand_t, cand_base, n);
        int hsize = 0;
        long long hsum = 0;
        for (int i = 0; i < n; i++) {
            hpush(heap, &hsize, &hsum, cand_base[i]);
            if (hsize > k)
                hpop(heap, &hsize, &hsum);
            if (hsize == k) {
                long long total = hsum + (long long)k * ((cand_t[i] - j) / 5) * W;
                if (best < 0 || total < best)
                    best = total;
            }
        }
    }
    return best;
}

// int main(void)
// {
//     int n, k;
//     long long b, c;
//     if (scanf("%d %d %lld %lld", &n, &k, &b, &c) != 4)
//         return 0;
//     static long long values[200005], shifted[200005];
//     static long long cand_t[200005], cand_base[200005], heap[200005];
//     for (int i = 0; i < n; i++) {
//         long long v;
//         scanf("%lld", &v);
//         values[i] = v;
//     }
//     printf("%lld\n", solver(values, n, k, b, c, shifted,
//                             cand_t, cand_base, heap));
//     return 0;
// }
