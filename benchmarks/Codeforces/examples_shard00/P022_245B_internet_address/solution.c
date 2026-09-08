/* Codeforces 245/B - Internet Address */
#include <stdio.h>
#include <string.h>

static void solver(const char *s, char *out)
{
    int n = (int)strlen(s), p = s[0] == 'h' ? 4 : 3, ru = -1, k = 0;
    for (int i = p + 1; i + 1 < n; ++i)
        if (s[i] == 'r' && s[i + 1] == 'u') { ru = i; break; }
    for (int i = 0; i < p; ++i) out[k++] = s[i];
    out[k++] = ':'; out[k++] = '/'; out[k++] = '/';
    for (int i = p; i < ru; ++i) out[k++] = s[i];
    out[k++] = '.'; out[k++] = 'r'; out[k++] = 'u';
    if (ru + 2 < n) {
        out[k++] = '/';
        for (int i = ru + 2; i < n; ++i) out[k++] = s[i];
    }
    out[k] = '\0';
}

int main(void)
{
    char s[64], out[72];
    if (scanf("%63s", s) != 1) return 0;
    solver(s, out); puts(out);
    return 0;
}
