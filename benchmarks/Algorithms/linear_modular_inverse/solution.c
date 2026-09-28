void linear_modular_inverse(int p, int *inverse)

{
    inverse[1] = 1;

    for (int i = 2; i < p; ++i) {
        int quotient = p / i;
        int remainder = p % i;
        
        inverse[i] = ((p - quotient) * inverse[remainder]) % p;
    }
}
