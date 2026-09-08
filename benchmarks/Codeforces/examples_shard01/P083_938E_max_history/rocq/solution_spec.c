/*
 * Codeforces 938/E - Max History  (rating 2300, COMBINATORICS)
 *
 * An element v is added to f exactly when it becomes the running maximum and
 * is later beaten.  It becomes the running maximum iff it appears before every
 * element >= v (ties block it too), which happens in n!/g of the permutations,
 * where g counts the elements >= v.  It is beaten iff some element is strictly
 * greater.  So the answer is the sum of v * n!/g over the elements that have a
 * strictly larger one.
 */

// #include <stdio.h>
// #include <stdlib.h>

/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P083_938E_max_history.rocq.spec_lib */
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/

#define MOD 1000000007LL

// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 50000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;

static long long power(long long b, long long e)
{
    long long r = 1;
    b %= MOD;
    while (e) {
        if (e & 1)
            r = r * b % MOD;
        b = b * b % MOD;
        e >>= 1;
    }
    return r;
}

/* solver: sum of f over all n! permutations, modulo 1e9+7.  Sorts a[]. */
static long long solver(int *a, int n)
/*@ With (values : list Z)
    Require
      1 <= n && n <= 1000000 && (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) &&
      exists (a_after : list Z), Permutation(values, a_after) && IntArray::full(a, n, a_after)
*/
{
    // qsort(a, n, sizeof *a, cmp_int);
    quicksort(a, n);
    long long fact = 1;
    for (int i = 2; i <= n; i++)
        fact = fact * i % MOD;
    long long total = 0;
    for (int i = 0; i < n; i++) {
        int j = i;
        while (j < n && a[j] == a[i])
            j++;
        if (j < n) {                      /* something strictly larger exists */
            long long g = n - i;          /* elements >= a[i] */
            long long share = fact % MOD * power(g % MOD, MOD - 2) % MOD;
            long long cnt = j - i;
            total = (total + cnt % MOD * (a[i] % MOD) % MOD * share) % MOD;
        }
        i = j - 1;
    }
    return total;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int a[1000006];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%lld\n", solver(a, n));
//     return 0;
// }
