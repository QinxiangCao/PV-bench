/*
 * Codeforces 535/C - Tavas and Karafs  (rating 1900, BINARY SEARCH)
 *
 * The prefix l..r can be eaten in t m-bite moves iff the tallest karafs fits
 * (s_r <= t) and the total height fits (sum <= t*m).  Both conditions get
 * harder as r grows, so binary search the largest feasible r.
 */

// #include <stdio.h>

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P065_535C_tavas_and_karafs.rocq.spec_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Spec : Z -> Z -> list(Z * Z * Z) -> list Z -> Prop)
*/

/* height: s_i = A + (i-1)*B. */
static long long height(long long A, long long B, long long i)
{
    return A + (i - 1) * B;
}

/* range_sum: sum of s_l .. s_r (arithmetic progression). */
static long long range_sum(long long A, long long B, long long l, long long r)
{
    long long cnt = r - l + 1;
    return (height(A, B, l) + height(A, B, r)) * cnt / 2;
}

/* solver: pure.  Largest r with l <= r that can be eaten, or -1. */
static long long answer_query(long long A, long long B, long long l,
                              long long t, long long m)
{
    if (height(A, B, l) > t)
        return -1;
    long long lo = l, hi = l;
    while (height(A, B, hi) <= t)         /* find an upper bound first */
        hi *= 2;
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;
        if (height(A, B, mid) <= t && range_sum(A, B, l, mid) <= t * m)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

/* solver: complete case.  Answer the entire logical query list. */
static void solver(long long A, long long B, const long long *ql,
                   const long long *qt, const long long *qm, int n,
                   long long *out)
/*@ With (queries : list(Z*Z*Z)) (left_limits : list Z) (times : list Z) (maxima : list Z)
    Require
      1 <= A && A <= 1000000 && 1 <= B && B <= 1000000 &&
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= fst(fst(queries[i])) && fst(fst(queries[i])) <= 1000000 && 1 <= snd(fst(queries[i])) && snd(fst(queries[i])) <= 1000000 && 1 <= snd(queries[i]) && snd(queries[i]) <= 1000000)) && n == Zlength(queries) && Zlength(left_limits) == n && Zlength(times) == n && Zlength(maxima) == n && (forall i, (0 <= i && i < n) => (left_limits[i] == fst(fst(queries[i])) && times[i] == snd(fst(queries[i])) && maxima[i] == snd(queries[i]))) && Int64Array::full(ql, n, left_limits) * Int64Array::full(qt, n, times) * Int64Array::full(qm, n, maxima) * Int64Array::full_shape(out, n)
    Ensure
      exists (result : list Z), Spec(A, B, queries, result) && Int64Array::full(ql, n, left_limits) * Int64Array::full(qt, n, times) * Int64Array::full(qm, n, maxima) * Int64Array::full(out, n, result)
*/
{
    for (int i = 0; i < n; i++)
        out[i] = answer_query(A, B, ql[i], qt[i], qm[i]);
}

// int main(void)
// {
//     long long A, B;
//     int n;
//     if (scanf("%lld %lld %d", &A, &B, &n) != 3)
//         return 0;
//     static long long ql[100005], qt[100005], qm[100005], out[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%lld %lld %lld", &ql[i], &qt[i], &qm[i]);
//     solver(A, B, ql, qt, qm, n, out);
//     for (int i = 0; i < n; i++)
//         printf("%lld\n", out[i]);
//     return 0;
// }
