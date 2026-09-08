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
/*@ Extern Coq
      (MRRotation : list Z -> Z -> list Z)
      (MRFirstMinimalRotationAt : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.minimal_representation.rocq.spec_lib */

int minimal_representation(int *a, int n, int *b, int *out)
/*@ With (l : list Z) (best : Z)
    Require
      1 <= n && n <= 1000 &&
      Zlength(l) == n &&
      0 <= best && best < n &&
      MRFirstMinimalRotationAt(l, best) &&
      IntArray::full(a, n, l) *
      IntArray::undef_full(b, 2 * n) *
      IntArray::undef_full(out, n)
    Ensure
      exists bl,
      __return == best &&
      MRFirstMinimalRotationAt(l, __return) &&
      IntArray::full(a, n, l) *
      IntArray::full(b, 2 * n, bl) *
      IntArray::full(out, n, MRRotation(l, __return))
 */
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
