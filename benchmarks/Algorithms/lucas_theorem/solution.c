int modular_power(int base, int exponent, int modulus)
;

int binomial_digit_mod_prime(int upper, int lower, int prime)

{
    if (lower > upper) {
        return 0;
    }

    if (lower > upper - lower) {
        lower = upper - lower;
    }

    int numerator = 1;
    int denominator = 1;

    for (int i = 1; i <= lower; ++i) {
        int factor = upper - lower + i;
        long long numerator_product = (long long)numerator * factor;
        long long denominator_product = (long long)denominator * i;

        numerator = (int)(numerator_product % prime);
        denominator = (int)(denominator_product % prime);
    }

    int inverse = modular_power(denominator, prime - 2, prime);
    long long answer = (long long)numerator * inverse;
    return (int)(answer % prime);
}

int lucas_theorem(int n, int m, int prime)

{
    int upper = n + m;
    int lower = n;
    int result = 1;

    while (upper > 0 || lower > 0) {
        int upper_digit = upper % prime;
        int lower_digit = lower % prime;

        if (lower_digit > upper_digit) {
            return 0;
        }

        int digit_binomial =
            binomial_digit_mod_prime(upper_digit, lower_digit, prime);
        long long product = (long long)result * digit_binomial;
        result = (int)(product % prime);

        upper /= prime;
        lower /= prime;
    }

    return result;
}
