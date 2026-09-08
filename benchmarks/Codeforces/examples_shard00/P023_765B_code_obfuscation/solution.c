/* Codeforces 765/B - Code obfuscation */
#include <stdio.h>

static int solver(const char *s)
{
    char next = 'a';
    for (int i = 0; s[i]; ++i) {
        if (s[i] > next) return 0;
        if (s[i] == next && next < 'z') ++next;
    }
    return 1;
}

int main(void)
{
    char s[505];
    if (scanf("%504s", s) != 1) return 0;
    puts(solver(s) ? "YES" : "NO");
    return 0;
}
