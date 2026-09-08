void optimized_selection_sort(int *a, int n)

{
    int i;

    for (i = 0; i + 1 < n; ++i) {
        int min_index = i;
        int j;

        for (j = i + 1; j < n; ++j) {
            if (a[j] < a[min_index]) {
                min_index = j;
            }
        }

        /* Avoid the three writes when the current element is already minimal. */
        if (min_index != i) {
            int tmp = a[i];
            a[i] = a[min_index];
            a[min_index] = tmp;
        }
    }
}
