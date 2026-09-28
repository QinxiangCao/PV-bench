/* Codeforces 1989/E - Distance to Different */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#define MOD 998244353LL
#define AT(a, i, j) (a)[(size_t)(i) * W + (j)]

static long long solver(int n,
                        int k)

{
    int W = k + 1;
    long long *dp = calloc((size_t)(n + 1) * W, sizeof(*dp)),
              *pref = calloc((size_t)(n + 1) * W, sizeof(*pref));

    for (int i = 1; i <= n; ++i)
    {

        AT(dp, i, 1) = 1;
        AT(pref, i, 1) = (AT(pref, i - 1, 1) + 1) % MOD;
    }

    for (int j = 2; j <= k; ++j)
    {

        for (int i = 1; i <= n; ++i)
        {

            long long val = AT(pref, i - 1, j - 1);
            if (i >= 3)
            {

                val -= AT(dp, i - 2, j - 1);
            }
            if (j == k)
            {

                val += AT(pref, i - 1, k);
                if (i >= 3)
                {

                    val -= AT(dp, i - 2, k);
                }
            }

            AT(dp, i, j) = (val % MOD + MOD) % MOD;

            AT(pref, i, j) = (AT(pref, i - 1, j) + AT(dp, i, j)) % MOD;
        }
    }

    long long ans = AT(dp, n, k);
    if (n >= 2)
    {

        ans = (ans + AT(dp, n - 2, k - 1) + AT(dp, n - 2, k)) % MOD;
    }

    free(dp);
    free(pref);
    return ans;
}
int main(void)
{
    int n, k;
    if (scanf("%d %d", &n, &k) != 2)
        return 0;
    printf("%lld\n", solver(n, k));
    return 0;
}
