int minimal_representation(int *a, int n, int *out)

{
    int b[2000];
    int p = 0;

    while (p < n) {
        b[p] = a[p];
        b[n + p] = a[p];
        ++p;
    }

    int i = 0;
    int j = 1;
    int k = 0;

    while (i < n && j < n) {
        k = 0;

        while (k < n && b[i + k] == b[j + k]) {
            ++k;
        }

        if (k == n) {
            break;
        }

        if (b[i + k] > b[j + k]) {
            i = i + k + 1;
            if (i == j) {
                ++i;
            }
        }
        else {
            j = j + k + 1;
            if (i == j) {
                ++j;
            }
        }
    }

    if (i < j) {
        p = i;
    }
    else {
        p = j;
    }

    k = 0;

    while (k < n) {
        out[k] = b[p + k];
        ++k;
    }

    return p;
}
