int rod_cutting(const int *price, int *revenue, int n)

{
    int j;

    revenue[0] = 0;

    for (j = 1; j <= n; ++j) {
        int best = 0;
        int i;

        for (i = 1; i <= j; ++i) {

            int candidate = price[i] + revenue[j - i];
            if (best < candidate) {
                best = candidate;
            }
        }
        revenue[j] = best;
    }

    return revenue[n];
}
