int modular_mul(int a, int b, int modulus)

{
    int res = 0;
    int flag = 1;
    if (b < 0) {
        b = -b;
        flag = -1;
    }

    while (b > 0) {
        if (b % 2 == 1) {
            res = (res + a) % modulus;
        }
        b = b / 2;
        a = (a + a) % modulus;
    }
    return res * flag;
}
