/*
 * Codeforces 509/E - Pretty Song  (rating 2000, MATH)
 *
 * Group the substrings by length L: their total vowel count is
 * sum_{i=L..n} p_i - sum_{i=0..n-L} p_i, where p is the vowel prefix count.
 * Prefix sums of p make each length O(1), and each contributes that total / L.
 */

#include <stdio.h>

/* solver: exact whole-case representation.  term[L-1] is the integer total
 * number of vowels over all substrings of length L.  The mathematical result
 * is exactly sum term[L-1]/L; no floating-point value crosses the contract. */
static void solver(const char *s, int n, long long *term,
                   long long *pre, long long *pp)
{
    pre[0] = 0;
    for (int i = 0; i < n; i++) {
        char c = s[i];
        int v = (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' ||
                 c == 'Y');
        pre[i + 1] = pre[i] + v;
    }
    pp[0] = pre[0];
    for (int i = 1; i <= n; i++)
        pp[i] = pp[i - 1] + pre[i];       /* prefix sums of the prefix counts */
    for (int L = 1; L <= n; L++) {
        long long hi = pp[n] - pp[L - 1]; /* sum of pre[L..n] */
        long long lo = pp[n - L];         /* sum of pre[0..n-L] */
        term[L - 1] = hi - lo;
    }
}

int main(void)
{
    static char s[500005];
    if (scanf("%500004s", s) != 1)
        return 0;
    int n = 0;
    while (s[n])
        n++;
    static long long term[500005], pre[500006], pp[500006];
    solver(s, n, term, pre, pp);
    long double total = 0;
    for (int L = 1; L <= n; L++)
        total += (long double)term[L - 1] / L;
    printf("%.7Lf\n", total);
    return 0;
}
