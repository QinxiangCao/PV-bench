/*@ Extern Coq
      (MRRotation : list Z -> Z -> list Z)
      (MRFirstMinimalRotationAt : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.minimal_representation.rocq.spec_lib */

int minimal_representation(int *a, int n, int *out)
/*@ With (l : list Z) (best : Z)
    Require
      1 <= n && n <= 1000 &&
      Zlength(l) == n &&
      0 <= best && best < n &&
      MRFirstMinimalRotationAt(l, best) &&
      IntArray::full(a, n, l) *
      IntArray::undef_full(out, n)
    Ensure
      MRFirstMinimalRotationAt(l, __return) &&
      IntArray::full(a, n, l) *
      IntArray::full(out, n, MRRotation(l, __return))
 */
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
