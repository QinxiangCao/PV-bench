/* Codeforces 1729/F - Kirei and the Linear Function */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

static void
solver(const char *s, int w, int m, const int *ql, const int *qr, const int *qk, int *out1,
       int *out2)

{

    int n = (int)strlen(s),
        *pre = calloc((size_t)n + 1, sizeof(*pre));

    for (int i = 0; i < n; ++i)
        pre[i + 1] = pre[i] + s[i] - '0';
    int pos[18];

    for (int r = 0; r < 9; ++r)
    {
        pos[2 * r] = -1;
        pos[2 * r + 1] = -1;
    }

    for (int i = 0; i + w <= n; ++i)
    {
        int r = (pre[i + w] - pre[i]) % 9;

        if (pos[2 * r] < 0)
            pos[2 * r] = i + 1;
        else if (pos[2 * r + 1] < 0)
            pos[2 * r + 1] = i + 1;
    }

    for (int z = 0; z < m; ++z)
    {
        int l = ql[z], r = qr[z], k = qk[z], v = (pre[r] - pre[l - 1]) % 9, best1 = 1 << 30,
            best2 = 1 << 30;

        for (int a = 0; a < 9; ++a)
        {
            int b = (k - a * v) % 9;
            if (b < 0)
                b += 9;

            if (pos[2 * a] < 0)
                continue;
            int p1 = pos[2 * a], p2 = (a == b) ? pos[2 * b + 1] : pos[2 * b];
            if (p2 < 0)
                continue;
            if (p1 < best1 || (p1 == best1 && p2 < best2))
            {
                best1 = p1;
                best2 = p2;
            }
        }

        out1[z] = best1 == (1 << 30) ? -1 : best1;
        out2[z] = best1 == (1 << 30) ? -1 : best2;
    }

    free(pre);
}
int main(void)
{
    int t;
    scanf("%d", &t);
    while (t--)
    {
        char *s = malloc(200005);
        scanf("%s", s);
        int w, m;
        scanf("%d %d", &w, &m);
        int *l = malloc((size_t)m * sizeof(*l)), *r = malloc((size_t)m * sizeof(*r)),
            *k = malloc((size_t)m * sizeof(*k)), *o1 = malloc((size_t)m * sizeof(*o1)),
            *o2 = malloc((size_t)m * sizeof(*o2));
        for (int i = 0; i < m; ++i)
            scanf("%d %d %d", &l[i], &r[i], &k[i]);
        solver(s, w, m, l, r, k, o1, o2);
        for (int i = 0; i < m; ++i)
            printf("%d %d\n", o1[i], o2[i]);
        free(l);
        free(r);
        free(k);
        free(o1);
        free(o2);
        free(s);
    }
    return 0;
}
