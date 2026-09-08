/*
 * Compute the modular inverses of 1, ..., p - 1 in linear time.
 *
 * For a prime p and 2 <= i < p, write p = (p / i) * i + p % i.
 * Since 1 <= p % i < i, its inverse has already been computed.  Therefore
 *
 *   inverse[i] = (p - p / i) * inverse[p % i] (mod p).
 *
 * The verification contract supplies the primality and writable-array
 * assumptions.  The upper bound p <= 46340 keeps the product in signed
 * 32-bit range.
 */

void linear_modular_inverse(int p, int *inverse)

{
    inverse[1] = 1;

    for (int i = 2; i < p; ++i) {
        int quotient = p / i;
        int remainder = p % i;

        inverse[i] = ((p - quotient) * inverse[remainder]) % p;
    }
}
