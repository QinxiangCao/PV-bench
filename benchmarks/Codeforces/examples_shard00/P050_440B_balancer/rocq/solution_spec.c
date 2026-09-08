/* Codeforces 440/B - Balancer */
// #include <stdio.h>

/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P050_440B_balancer.rocq.spec_lib */

static long long solver(const long long *a, int n)

/*@ With (values : list Z)
    Require
      1 <= Zlength(values) && Zlength(values) <= 50000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (0 <= values[i] && values[i] <= 1000000000)) &&
      Pre(values) &&
      n == Zlength(values) &&
      Int64Array::full(a, n, values)
    Ensure
      Spec(values, __return) &&
      Int64Array::full(a, n, values)
*/

{
    long long sum = 0;
    
    for (int i = 0; i < n; ++i) sum += a[i];
    long long target = sum / n, balance = 0, answer = 0;
    
    for (int i = 0; i + 1 < n; ++i) {
        balance += a[i] - target;
        answer += balance < 0 ? -balance : balance;
    }
    return answer;
}

// int main(void)
// {
//     int n; if (scanf("%d", &n) != 1) return 0;
//     long long a[50000]; for (int i = 0; i < n; ++i) scanf("%lld", &a[i]);
//     printf("%lld\n", solver(a, n));
//     return 0;
// }
