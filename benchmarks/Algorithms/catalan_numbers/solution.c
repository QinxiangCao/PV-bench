#include "int_array_def.h"

int id(int n, int x, int y)

{
    return x * (n + 1)  + y;
}

int solve(int n)

{
    int f[64];

    for (int i = 0; i <= n; i++) {

        for (int j = 0; j <= n; j++) {
            if (i == 0) {
                f[id(n, i, j)] = 1;
            }
            else if (j == 0) {

                f[id(n, i, j)] = f[id(n, i-1, j+1)];
            }
            else {

                f[id(n, i, j)] = f[id(n, i-1, j+1)] + f[id(n, i, j-1)];
            }
        }
    }

    int result = f[id(n, n, 0)];

    return result;
}
