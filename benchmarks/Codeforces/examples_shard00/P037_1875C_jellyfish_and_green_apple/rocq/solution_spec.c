/* Codeforces 1875/C - Jellyfish and Green Apple */
// #include <stdio.h>

static long long gcdll(long long a, long long b)

{
    
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
