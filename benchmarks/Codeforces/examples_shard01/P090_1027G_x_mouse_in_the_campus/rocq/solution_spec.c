/*
 * Codeforces 1027/G - X-mouse in the Campus  (rating 2600, NUMBER THEORY)
 *
 * Room r with gcd(r, m) = g stays in that gcd class forever, and multiplying
 * by x acts on r/g inside the units of Z_{m/g}.  So the rooms with a fixed
 * d = m/g form phi(d)/ord_d(x) cycles, each needing one trap, and room 0 needs
 * one more.  Orders multiply through the CRT, so ord_d(x) is the lcm of the
 * orders modulo the prime powers of d, and the divisors of m are enumerated
 * carrying (phi, ord) along.
 */

// #include <stdio.h>
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P090_1027G_x_mouse_in_the_campus.rocq.spec_lib */
/*@ Extern Coq
      (Pre : Z -> Z -> Prop)
      (Spec : Z -> Z -> Z -> Prop)
*/

static unsigned long long pr[64], pe[64];   /* prime factors of m and exponents */
static int nf;

/* mulmod / powmod on 64-bit moduli up to 1e14.
 *
 * mulmod doubles a while walking the bits of b, so no product ever forms: the
 * modulus is at most 1e14, so 2 * modulus still fits an unsigned long long and
 * every intermediate below stays under it. */
static unsigned long long mulmod(unsigned long long a, unsigned long long b,
                                 unsigned long long modulus)
{
    unsigned long long r = 0;
    a %= modulus;
    b %= modulus;
    while (b) {
        if (b & 1) {
            r += a;
            if (r >= modulus)
                r -= modulus;
        }
        a <<= 1;
        if (a >= modulus)
            a -= modulus;
        b >>= 1;
    }
    return r;
}

static unsigned long long powmod(unsigned long long b, unsigned long long e,
                                 unsigned long long modulus)
{
    unsigned long long r = 1 % modulus;
    b %= modulus;
    while (e) {
        if (e & 1)
            r = mulmod(r, b, modulus);
        b = mulmod(b, b, modulus);
        e >>= 1;
    }
    return r;
}

static unsigned long long gcd_(unsigned long long a, unsigned long long b)
{
    while (b) {
        unsigned long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* order: multiplicative order of x modulo mod, given phi(mod). */
static unsigned long long order(unsigned long long x, unsigned long long modulus,
                                unsigned long long phi)
{
    if (modulus == 1)
        return 1;
    unsigned long long ord = phi, t = phi;
    for (unsigned long long q = 2; q * q <= t; q++)
        if (t % q == 0) {
            while (t % q == 0)
                t /= q;
            while (ord % q == 0 && powmod(x, ord / q, modulus) == 1)
                ord /= q;
        }
    if (t > 1)
        while (ord % t == 0 && powmod(x, ord / t, modulus) == 1)
            ord /= t;
    return ord;
}

static unsigned long long x_, total_;

/* walk: enumerate the divisors of m, carrying phi(d) and ord_d(x). */
static void walk(int i, unsigned long long d, unsigned long long phi,
                 unsigned long long ord)
{
    if (i == nf) {
        if (d > 1)
            total_ += phi / ord;
        return;
    }
    walk(i + 1, d, phi, ord);             /* exponent 0 */
    unsigned long long p = pr[i], pk = 1, ph = 1;
    for (unsigned long long e = 1; e <= pe[i]; e++) {
        pk *= p;
        ph = (e == 1) ? p - 1 : ph * p;
        unsigned long long o = order(x_ % pk, pk, ph);
        unsigned long long g = gcd_(ord, o);
        walk(i + 1, d * pk, phi * ph, ord / g * o);
    }
}

/* solver: minimum number of traps. */
static unsigned long long solver(unsigned long long m, unsigned long long x)
/*@
    Require
      2 <= m && m <= 100000000000000 && 1 <= x && x < m &&
      Pre(m, x) &&
      UInt64Array::undef_full(pr, 64) * UInt64Array::undef_full(pe, 64) *
      has_int_permission(&nf) * has_permission(&x_) * has_permission(&total_)
    Ensure
      Spec(m, x, __return) &&
      exists (factor_count : Z) (base : Z) (accumulator : Z),
        0 <= factor_count && factor_count <= 64 &&
        UInt64Array::seg_shape(pr, 0, factor_count) *
        UInt64Array::undef_seg(pr, factor_count, 64) *
        UInt64Array::seg_shape(pe, 0, factor_count) *
        UInt64Array::undef_seg(pe, factor_count, 64) *
        store_int(&nf, factor_count) * store(&x_, base) * store(&total_, accumulator)
*/
{
    unsigned long long t = m;
    nf = 0;
    for (unsigned long long p = 2; p * p <= t; p++)
        if (t % p == 0) {
            pr[nf] = p;
            pe[nf] = 0;
            while (t % p == 0) {
                t /= p;
                pe[nf] = pe[nf] + 1;
            }
            nf++;
        }
    if (t > 1) {
        pr[nf] = t;
        { pe[nf] = 1; nf++; }
    }
    x_ = x;
    total_ = 0;
    walk(0, 1, 1, 1);
    return total_ + 1;                    /* room 0 */
}

// int main(void)
// {
//     unsigned long long m, x;
//     if (scanf("%llu %llu", &m, &x) != 2)
//         return 0;
//     printf("%llu\n", solver(m, x));
//     return 0;
// }
