/*
 * The verified exgcd case supplies this interface.  In particular, x and y
 * are Bezout coefficients when the call returns.
 */
int exgcd(int a, int b, int *x, int *y)
;

/*
 * Return the canonical representative of the inverse of a modulo modulus.
 * The precondition restricts this small example to the usual coprime,
 * positive inputs for which an inverse exists.
 */
int modular_inverse(int a, int modulus)

{
    int x;
    int y;
    int g = exgcd(a, modulus, &x, &y);

    /* The precondition and the exgcd contract imply g == 1. */
    int inverse = x % modulus;
    if (inverse < 0) {
        inverse += modulus;
    }
    return inverse;
}
