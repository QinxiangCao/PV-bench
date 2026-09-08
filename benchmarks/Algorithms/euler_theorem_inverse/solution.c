/*
 * Compute a modular inverse with Euler's theorem.
 *
 * If a and modulus are coprime, Euler's theorem gives
 *
 *     a ^ phi(modulus) = 1 (mod modulus),
 *
 * so a ^ (phi(modulus) - 1) is an inverse of a modulo modulus.
 * This small example deliberately uses int throughout, following 2.cpp.
 */

int euler_phi(int value)

{
    int result = value;

    for (int factor = 2; factor * factor <= value; ++factor) {
        if (value % factor == 0) {

            while (value % factor == 0) {
                value /= factor;
            }

            result = result / factor * (factor - 1);
        }
    }

    if (value != 1) {
        result = result / value * (value - 1);
    }

    return result;
}

int modular_power(int base, int exponent, int modulus)

{
    int result = 1;

    while (exponent > 0) {
        if (exponent % 2 == 1) {
            result = result * base % modulus;
        }
        base = base * base % modulus;
        exponent /= 2;
    }

    return result;
}

int euler_theorem_inverse(int value, int modulus)

{
    int exponent = euler_phi(modulus) - 1;

    return modular_power(value, exponent, modulus);
}
