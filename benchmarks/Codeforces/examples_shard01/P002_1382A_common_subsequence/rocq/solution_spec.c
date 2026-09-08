/*
 * Codeforces 1382/A - Common Subsequence  (rating 800, BRUTE FORCE)
 *
 * A common subsequence of minimum length has length 1 whenever the two arrays
 * share any value at all, so it is enough to look for one common element; if
 * none exists no common non-empty subsequence exists either.
 */

// #include <stdio.h>
#include "string.h"

/*@ Extern Coq
      (Spec : list Z -> list Z -> option (list Z) -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P002_1382A_common_subsequence.rocq.spec_lib */

#define MAXV 1001

/* solver: pure.  Returns a value present in both arrays, or 0 if there is
 * none (values are >= 1, so 0 is safe as "not found"). */
static int solver(const int *a, int n, const int *b, int m)
/*@ With (left : list Z) (right : list Z)
    Require
      1 <= n && n <= 1000 && 1 <= m && m <= 1000 && 
      (forall i, (0 <= i && i < n) => (1 <= left[i] && left[i] <= 1000)) && 
      (forall i, (0 <= i && i < m) => (1 <= right[i] && right[i] <= 1000)) &&
      n == Zlength(left) && m == Zlength(right) && 
      IntArray::full(a, n, left) * IntArray::full(b, m, right)
    Ensure
      exists (out : option (list Z)),
        Spec(left, right, out) &&
        ((out == None && __return == 0) || out == Some(cons(__return, nil))) && IntArray::full(a, n, left) * IntArray::full(b, m, right)
*/
{
    char seen[MAXV];
    memset(seen, 0, sizeof seen);
    for (int i = 0; i < n; i++)
        seen[a[i]] = 1;
    for (int j = 0; j < m; j++)
        if (seen[b[j]])
            return b[j];
    return 0;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n, m;
//         static int a[1005], b[1005];
//         scanf("%d %d", &n, &m);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         for (int j = 0; j < m; j++)
//             scanf("%d", &b[j]);
//         int v = solver(a, n, b, m);
//         if (v)
//             printf("YES\n1 %d\n", v);
//         else
//             printf("NO\n");
//     }
//     return 0;
// }
