/* Codeforces 48/A - Rock-paper-scissors */
#include <stdio.h>
#include <string.h>

static int beats(const char *a, const char *b)
{
    return (!strcmp(a, "rock") && !strcmp(b, "scissors")) ||
           (!strcmp(a, "scissors") && !strcmp(b, "paper")) ||
           (!strcmp(a, "paper") && !strcmp(b, "rock"));
}

static char solver(const char g[3][16])
{
    const char label[] = "FMS";
    for (int i = 0; i < 3; ++i)
        if (beats(g[i], g[(i + 1) % 3]) && beats(g[i], g[(i + 2) % 3]))
            return label[i];
    return '?';
}

int main(void)
{
    char g[3][16];
    if (scanf("%15s %15s %15s", g[0], g[1], g[2]) != 3) return 0;
    printf("%c\n", solver(g));
    return 0;
}
