/*
 * Interface supplied by the verified extended Euclidean algorithm case.
 * This case uses only its contract; the exgcd implementation is verified
 * separately and is intentionally not repeated here.
 */
int exgcd(int a, int b, int *x, int *y)
;

/*
 * Interface supplied by the separately verified modular-multiplication case.
 * This case uses only its contract and intentionally does not repeat its body.
 */
int modular_mul(int a, int b, int modulus)
;

/*
 * Solve a compatible system of congruences with the extended Chinese
 * remainder theorem:
 *
 *     answer = residues[i] (mod moduli[i]),  0 <= i < n.
 *
 * The returned answer is the least nonnegative common residue and
 * *combined_modulus is the least common multiple of all input moduli.
 *
 * This implementation intentionally mirrors 3.cpp: start from the first
 * congruence, then use exgcd and modular_mul to merge every remaining
 * congruence into the current answer/lcm pair.  It deliberately uses int
 * throughout; the long-long and data-range-engineering variants are out of
 * scope.
 */
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
