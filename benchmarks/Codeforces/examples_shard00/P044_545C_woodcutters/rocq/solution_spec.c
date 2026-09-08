/* Codeforces 545/C - Woodcutters */
// #include <stdio.h>
// #include <stdlib.h>

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : list (Z*Z) -> Prop)
      (Spec : list (Z*Z) -> Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P044_545C_woodcutters.rocq.spec_lib */

static int solver(const long long *x, const long long *h,
                  int n) 

/*@ With (trees : list (Z*Z))
             (positions heights : list Z)
    Require
      1 <= Zlength(trees) && Zlength(trees) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(trees)) => ((1 <= fst(trees[i]) && fst(trees[i]) <= 1000000000) && (1 <= snd(trees[i]) && snd(trees[i]) <= 1000000000))) &&
      Pre(trees) &&
      n == Zlength(trees) &&
      Zlength(positions) == n && Zlength(heights) == n &&
      (forall i, (0 <= i && i < n) =>
        (fst(trees[i]) == positions[i] &&
         snd(trees[i]) == heights[i])) &&
      Int64Array::full(x, n, positions) *
      Int64Array::full(h, n, heights)
    Ensure
      Spec(trees, __return) &&
      Int64Array::full(x, n, positions) *
      Int64Array::full(h, n, heights)
*/

{
    if (n <= 2)
        return n;
    int answer = 2;
    long long occupied = x[0];
    
    for (int i = 1; i + 1 < n; ++i)
    {
        if (x[i] - h[i] > occupied)
        {
            ++answer;
            occupied = x[i];
        }
        else if (x[i] + h[i] < x[i + 1])
        {
            ++answer;
            occupied = x[i] + h[i];
        }
        else
            occupied = x[i];
    }
    return answer;
}

// int main(void)
// {
//     int n; if (scanf("%d", &n) != 1) return 0;
//     long long *x = malloc((size_t)n * sizeof(*x)), *h = malloc((size_t)n * sizeof(*h));
//     for (int i = 0; i < n; ++i) scanf("%lld %lld", &x[i], &h[i]);
//     printf("%d\n", solver(x, h, n)); free(x); free(h);
//     return 0;
// }
