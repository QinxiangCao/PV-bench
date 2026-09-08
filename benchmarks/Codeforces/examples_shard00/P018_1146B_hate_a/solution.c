/* Codeforces 1146/B - Hate "A" */
#include <stdio.h>
#include <string.h>

static int solver(const char *given, char *out)
{
    static char stripped[100005];
    strcpy(out, given);
    int n = (int)strlen(out), k = 0;
    for (int i = 0; i < n; ++i) if (out[i] != 'a') stripped[k++] = out[i];
    if (k & 1) return 0;
    int suffix = k / 2, prefix = n - suffix;
    for (int i = prefix; i < n; ++i) if (out[i] == 'a') return 0;
    for (int i = 0; i < suffix; ++i)
        if (stripped[i] != out[prefix + i]) return 0;
    out[prefix] = '\0';
    return 1;
}

int main(void)
{
    static char t[100005], out[100005];
    if (scanf("%100004s", t) != 1) return 0;
    puts(solver(t, out) ? out : ":(");
    return 0;
}
