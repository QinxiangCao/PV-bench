/* Codeforces 1875/C - Jellyfish and Green Apple */
// #include <stdio.h>

/*@ Extern Coq
      (GcdValue : Z -> Z -> Z)
      (PowerOfTwo : Z -> Prop)
      (DyadicRemainderPrefix : Z -> Z -> Z -> Z -> Prop)
*/

static long long gcdll(long long a, long long b)
/*@ Require
      1 <= a && a <= 1000000000 &&
      1 <= b && b <= 1000000000 && emp
    Ensure
      __return == GcdValue(a@pre, b@pre) && emp
*/
{
    /*@ Inv Assert
      1 <= a && a <= 1000000000 &&
      0 <= b && b <= 1000000000 &&
      GcdValue(a, b) == GcdValue(a@pre, b@pre) && emp
    */
    while (b)
    {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P037_1875C_jellyfish_and_green_apple.rocq.spec_lib */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P037_1875C_jellyfish_and_green_apple.rocq.helper_lib */

static long long
solver(long long n,
       long long m) 

/*@ Require
      1 <= n && n <= 1000000000 &&
      1 <= m && m <= 1000000000
    Ensure
      Spec(n, m, __return)
*/

{
    long long d = m / gcdll(n, m);
    if (d & (d - 1))
        return -1;
    n %= m;
    long long answer = 0;
    /*@ Inv Assert
      1 <= n@pre && n@pre <= 1000000000 &&
      m == m@pre && 1 <= m@pre && m@pre <= 1000000000 &&
      d == m@pre / GcdValue(n@pre, m@pre) &&
      PowerOfTwo(d) &&
      0 <= n && n < m@pre &&
      0 <= answer && answer <= 30000000000 &&
      DyadicRemainderPrefix(n@pre % m@pre, m@pre, n, answer)
    */
    while (n)
    {
        answer += n;
        n = (2 * n) % m;
    }
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) { long long n, m; scanf("%lld %lld", &n, &m); printf("%lld\n", solver(n, m)); }
//     return 0;
// }
