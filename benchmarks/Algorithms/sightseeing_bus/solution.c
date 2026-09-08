int solve(int n, int m, int k, int *d, int *t, int *a, int *b,
          int *late, int *off, int *arr)

{
    int i;
    int j;
    int cur;
    int best;
    int pos;
    int cnt;
    int ans;

    for (i = 0; i < n; ++i) {
        late[i] = 0;
        off[i] = 0;
    }

    for (i = 0; i < m; ++i) {
        int x = a[i] - 1;
        int y = b[i] - 1;

        if (late[x] < t[i]) {
            late[x] = t[i];
        }
        off[y] = off[y] + 1;
    }

    cur = 0;

    for (i = 0; i < n; ++i) {
        arr[i] = cur;
        if (cur < late[i]) {
            cur = late[i];
        }
        if (i + 1 < n) {
            cur = cur + d[i];
        }
    }

    while (k > 0) {
        best = 0;
        pos = -1;

        for (i = 0; i + 1 < n; ++i) {
            if (d[i] > 0) {
                cnt = 0;

                for (j = i + 1; j < n; ++j) {
                    cnt = cnt + off[j];
                    if (arr[j] <= late[j]) {
                        break;
                    }
                }

                if (best < cnt) {
                    best = cnt;
                    pos = i;
                }
            }
        }

        if (pos < 0 || best == 0) {
            break;
        }
        d[pos] = d[pos] - 1;

        for (i = pos + 1; i < n; ++i) {
            arr[i] = arr[i] - 1;
            if (arr[i] < late[i]) {
                break;
            }
        }

        k = k - 1;
    }

    ans = 0;

    for (i = 0; i < m; ++i) {

        ans = ans + arr[b[i] - 1] - t[i];
    }
    return ans;
}
