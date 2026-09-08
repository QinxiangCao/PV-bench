/* Codeforces 1104/B - Game with string */
#include <stdio.h>

static int solver(const char *s)
{
    static char stack[100005];
    int top = 0, moves = 0;
    for (int i = 0; s[i]; ++i) {
        if (top && stack[top - 1] == s[i]) { --top; ++moves; }
        else stack[top++] = s[i];
    }
    return moves & 1;
}

int main(void)
{
    static char s[100005];
    if (scanf("%100004s", s) != 1) return 0;
    puts(solver(s) ? "Yes" : "No");
    return 0;
}
