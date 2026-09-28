/* Codeforces 887/A - Div. 64 */
#include <stdio.h>

static int solver(const char *s)
{
    int seen_one = 0, zeros = 0;
    for (int i = 0; s[i]; ++i) {
        if (s[i] == '1') seen_one = 1;
        else if (seen_one) ++zeros;
    }
    return zeros >= 6;
}

int main(void)
{
    char s[105];
    if (scanf("%104s", s) != 1) return 0;
    puts(solver(s) ? "yes" : "no");
    return 0;
}
