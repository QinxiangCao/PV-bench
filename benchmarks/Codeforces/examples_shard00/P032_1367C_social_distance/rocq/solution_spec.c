/* Codeforces 1367/C - Social Distance */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/*@ Extern Coq
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P032_1367C_social_distance.rocq.spec_lib */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

void *malloc(size_t size)
    /*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/
    ;

void free(void *ptr)
    /*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/
    ;

static int solver(char *s, int n, int k) 

/*@ With (seats : list Z)
    Require
      n == Zlength(seats) &&
      1 <= k && k <= Zlength(seats) && Zlength(seats) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(seats)) =>
        (seats[i] == 48 || seats[i] == 49)) &&
      Pre(k, seats) &&
      CharArray::full(s, n + 1, app(seats, cons(0, nil)))
    Ensure
      Spec(k, seats, __return) &&
      CharArray::full(s, n + 1, app(seats, cons(0, nil)))
*/

{
    int answer = 0, last = -k - 1;
    int *next = malloc((size_t)n * sizeof(*next))
        ;
    int nearest = n + k;
    
    for (int i = n - 1; i >= 0; --i)
    {
        if (s[i] == '1')
            nearest = i;
        next[i] = nearest;
    }

    for (int i = 0; i < n; ++i)
    {
        if (s[i] == '1')
        {
            last = i;
            continue;
        }
        if (i - last > k && next[i] - i > k)
        {
            ++answer;
            last = i;
        }
    }
    
    free(next);
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, k; char *s; scanf("%d %d", &n, &k);
//         s = malloc((size_t)n + 1); scanf("%s", s);
//         printf("%d\n", solver(s, n, k)); free(s);
//     }
//     return 0;
// }
