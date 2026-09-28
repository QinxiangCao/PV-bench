/* Codeforces 886/D - Restoration of string */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

static int solver(int n, char *const *words,
                  char *out)

{
    int next[26], prev[26], used[26] = {0};

    for (int i = 0; i < 26; ++i)
    {
        prev[i] = -1;
        next[i] = -1;
    }

    for (int z = 0; z < n; ++z)
    {

        int seen[26] = {0}, last = -1;
        const char *s = words[z];

        for (int i = 0; s[i]; ++i)
        {
            int c = s[i] - 'a';

            used[c] = 1;
            if (seen[c])
                return 0;
            seen[c] = 1;
            if (last >= 0)
            {
                if ((next[last] >= 0 && next[last] != c) || (prev[c] >= 0 && prev[c] != last))
                    return 0;
                next[last] = c;
                prev[c] = last;
            }
            last = c;
        }

    }
    int visited[26] = {0}, len = 0;

    for (int start = 0; start < 26; ++start)
        if (used[start] && prev[start] < 0)
        {
            int c = start;

            while (c >= 0 && !visited[c])
            {
                visited[c] = 1;
                out[len] = (char)('a' + c);
                ++len;
                c = next[c];
            }

        }

    for (int c = 0; c < 26; ++c)
        if (used[c] && !visited[c])
            return 0;

    out[len] = '\0';
    return 1;
}
int main(void)
{
    int n;
    if (scanf("%d", &n) != 1)
        return 0;
    char **words = malloc((size_t)n * sizeof(*words));
    for (int i = 0; i < n; ++i)
    {
        words[i] = malloc(100005);
        scanf("%100004s", words[i]);
    }
    char out[64];
    if (solver(n, words, out))
        puts(out);
    else
        puts("NO");
    for (int i = 0; i < n; ++i)
        free(words[i]);
    free(words);
    return 0;
}
