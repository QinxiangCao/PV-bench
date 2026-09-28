int exgcd(int a, int b, int *x, int *y)
;

int chinese_remainder_theorem(int n, int *remainders, int *moduli)

{
    int product = 1;

    for (int i = 0; i < n; ++i) {
        product *= moduli[i];
    }

    int result = 0;

    for (int i = 0; i < n; ++i) {
        int partial_product = product / moduli[i];
        int coefficient;
        int unused;

        exgcd(partial_product, moduli[i], &coefficient, &unused);

        int term = (int)(((long long)coefficient * partial_product) % product);
        term = (term * remainders[i]) % product;
        if (term < 0) {
            term += product;
        }

        result = (result + term) % product;
    }

    return result;
}
