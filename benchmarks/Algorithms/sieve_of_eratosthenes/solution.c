void solve(int n, int *f)

{

    for (int i = 1; i <= n; i++) {
        f[i] = 1;
    }
    f[1] = 0;
    f[2] = 1;

    for (int i = 2; i <= n; i++) {
        if (f[i] == 1) {

            for (int j = i * 2; j <= n; j = j + i) {
                f[j] = 0;
            }

        }

    }

}
