/*
 * Stable counting sort for values in the fixed range [0, 99].
 * The cumulative histogram gives the end of each value's bucket; walking the
 * input from right to left makes the placement phase stable.
 */
void sort(int *a, int n)

{
    int count[100];
    int output[100];

    for (int value = 0; value < 100; ++value) {
        count[value] = 0;
    }

    for (int i = 0; i < n; ++i) {

        ++count[a[i]];
    }

    for (int value = 1; value < 100; ++value) {
        count[value] += count[value - 1];
    }

    for (int i = n - 1; i >= 0; --i) {

        int value = a[i];

        --count[value];

        output[count[value]] = value;
    }

    for (int i = 0; i < n; ++i) {
        a[i] = output[i];
    }

}
