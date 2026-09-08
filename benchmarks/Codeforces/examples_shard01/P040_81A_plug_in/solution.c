/*
 * Codeforces 81/A - Plug-in  (rating 1400, IMPLEMENTATION)
 *
 * Push characters on a stack; whenever the incoming character equals the top,
 * pop instead, which cancels the pair and immediately exposes any pair that
 * the deletion has created.
 */

#include <stdio.h>

/* solver: pure.  Reduces s[0..n-1] into out (NUL-terminated), returning its
 * length. */
static int solver(const char *s, int n, char *out)
{
    int top = 0;
    for (int i = 0; i < n; i++) {
        if (top > 0 && out[top - 1] == s[i])
            top--;
        else
            { out[top] = s[i]; top++; }
    }
    out[top] = '\0';
    return top;
}

int main(void)
{
    static char s[200005], out[200005];
    if (scanf("%200004s", s) != 1)
        return 0;
    int n = 0;
    while (s[n])
        n++;
    solver(s, n, out);
    puts(out);
    return 0;
}
