int exgcd(int a, int b, int *x, int *y)
;

int modular_mul(int a, int b, int modulus)
;

int extended_chinese_remainder_theorem(int n,
                                      int *residues,
                                      int *moduli,
                                      int *combined_modulus)

{
    int answer = residues[0];
    int lcm = moduli[0];

    for (int i = 1; i < n; ++i) {
        int x;
        int y;
        int gcd = exgcd(lcm, moduli[i], &x, &y);
        int reduced_modulus = moduli[i] / gcd;

        x = modular_mul(x, (residues[i] - answer) / gcd, reduced_modulus);
        if (x < 0) {
            x += reduced_modulus;
        }

        answer = answer + x * lcm;
        lcm = lcm * reduced_modulus;
    }

    *combined_modulus = lcm;
    return answer;
}
