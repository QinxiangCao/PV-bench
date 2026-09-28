int modular_power(int a, int b, int modulus)

{
    int result = 1;

    while (b > 0) {
        if (b % 2 == 1) {
            result = (int)((long long)result * a % modulus);
        }
        a = (int)((long long)a * a % modulus);
        b /= 2;
    }

    return result;
}
