/*
 * Find the lexicographically smallest cyclic rotation of an integer sequence.
 *
 * The sequence is copied twice into b so that every cyclic rotation is
 * represented by one contiguous segment.  The two-candidate scan eliminates
 * at least one possible starting position after every mismatch, and therefore
 * runs in linear time.
 *
 * The verification case limits n to 1000.  The caller provides n initialized
 * elements in a, room for 2 * n elements in b, and room for n elements in out.
 * The function writes the smallest rotation to out and returns its zero-based
 * starting position in a.
 */

int minimal_representation(int *a, int n, int *b, int *out)

{
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
