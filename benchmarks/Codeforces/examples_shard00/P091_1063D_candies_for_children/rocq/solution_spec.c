// #include <stdio.h>
typedef long long i64;
/*@ Extern Coq
      (MaxResult : Z -> Z -> Z -> Prop)
      (MinResult : Z -> Z -> Z -> Prop)
      (QuotientBlock : Z -> Z -> Z -> Z -> Prop)
      (CandyFeasibleInterval : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (CandySearchPrefix : Z -> Z -> Z -> Z -> Z -> Prop)
      (CandySearchBlock : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (CandyArithmeticBest : Z -> Z -> Z -> Z -> Prop)
*/
static i64 maxll(i64 a, i64 b)

{
    return a > b ? a : b;
}
static i64 minll(i64 a, i64 b)

{
    return a < b ? a : b;
}
static i64 ceildiv(i64 a, i64 b)

{
    if (a <= 0)
        return a / b;
    return (a + b - 1) / b;
}
static void check(i64 L, i64 R, i64 q, i64 n, i64 x, i64 k, i64 add, i64 *best)

{
    i64 c = k - x + add, lo = L, hi = R;
    /* y = c-q*num; add=0 is normal, add=1 is the one-candy sweet last child. */
    if (q)
    {
        hi = minll(hi, (add ? c - 1 : c) / q);
        lo = maxll(lo, ceildiv(c - x, q));
    }
    else if ((add && c < 1) || (!add && c < 0) || c > x)
        return;
    lo = maxll(lo, ceildiv(c + n, q + 1));
    hi = minll(hi, (c + 2 * n - x) / (q + 1));
    
    if (lo <= hi && hi - n > *best)
        *best = hi - n;
}
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Z -> Prop)
*/

static i64 solver(i64 n, i64 l, i64 r,
                  i64 k) 
/*@
    Require
      1 <= n && n <= 100000000000 &&
      1 <= k && k <= 100000000000 &&
      1 <= l && l <= n &&
      1 <= r && r <= n
    Ensure
      Spec(n, l, r, k, __return)
*/
{
    i64 x = (r - l + n) % n + 1, z = k - 1, best = -1;
    
    for (i64 cur = n; cur <= 2 * n;)
    {
        i64 q = z / cur, R = q ? z / q : 2 * n;
        if (R > 2 * n)
            R = 2 * n;
        
        check(cur, R, q, n, x, k, 0, &best) ;
        check(cur, R, q, n, x, k, 1, &best) ;
        
        if (R == 2 * n)
            break;
        cur = R + 1;
    }
    return best;
}
// int main(void)
// {
//     i64 n, l, r, k;
//     if (scanf("%lld%lld%lld%lld", &n, &l, &r, &k) != 4)
//         return 0;
//     printf("%lld\n", solver(n, l, r, k));
//     return 0;
// }
