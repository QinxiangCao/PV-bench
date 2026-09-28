int exgcd(int a, int b, int *x, int *y)
;

int modular_inverse(int a, int modulus)

{
    int x;
    int y;
    int g = exgcd(a, modulus, &x, &y);

    int inverse = x % modulus;
    if (inverse < 0) {
        inverse += modulus;
    }
    return inverse;
}
