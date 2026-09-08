/* Codeforces 1082/C - Multi-Subject Competition */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;
typedef struct
{
    int subject, skill;
} Candidate;

static int cmp_candidate(const void *x, const void *y)
{
    const Candidate *a = x, *b = y;
    if (a->subject != b->subject)
        return (a->subject > b->subject) - (a->subject < b->subject);
    return (b->skill > a->skill) - (b->skill < a->skill);
}

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> list (Z*Z) -> Z -> Prop)
      (Permutation : list (Z * Z) -> list (Z * Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P046_1082C_multi_subject_competition.rocq.spec_lib */

/*@ Extern Coq
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (CandidatesSorted : list (Z*Z) -> Prop)
*/

void *calloc(unsigned long nmemb, unsigned long size)
    /*@ calloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, cap, repeat_Z(0, cap))
*/
    ;

void qsort(Candidate *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *))
    /*@ qsort_candidates
    With (contents : list (Z*Z)) (raw_contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      Zlength(raw_contents) == 2 * nmemb &&
      (forall i, (0 <= i && i < nmemb) =>
        (raw_contents[2 * i] == fst(contents[i]) &&
         raw_contents[2 * i + 1] == snd(contents[i]))) &&
      IntArray::full(base, 2 * nmemb, raw_contents)
    Ensure
      exists sorted raw_sorted,
        Permutation(contents, sorted) &&
        CandidatesSorted(sorted) &&
        Zlength(sorted) == nmemb &&
        Zlength(raw_sorted) == 2 * nmemb &&
        (forall i, (0 <= i && i < nmemb) =>
          (raw_sorted[2 * i] == fst(sorted[i]) &&
           raw_sorted[2 * i + 1] == snd(sorted[i]))) &&
        IntArray::full(base, 2 * nmemb, raw_sorted)
*/
    ;

void free(void *ptr)
    /*@ free_int64
    Require exists values cap,
      Int64Array::full(ptr, cap, values)
    Ensure emp
*/
    ;

static long long solver(Candidate *a, int n,
                        int m) 

/*@ With (students : list (Z*Z))
             (raw : list Z)
    Require
      1 <= Zlength(students) && Zlength(students) <= 100000 &&
      1 <= m && m <= 100000 &&
      (forall i, (0 <= i && i < Zlength(students)) => ((1 <= fst(students[i]) && fst(students[i]) <= m) && (-10000 <= snd(students[i]) && snd(students[i]) <= 10000))) &&
      n == Zlength(students) && Zlength(raw) == 2 * n &&
      (forall i, (0 <= i && i < n) =>
        (raw[2 * i] == fst(students[i]) &&
         raw[2 * i + 1] == snd(students[i]))) &&
      IntArray::full(a, 2 * n, raw)
    Ensure
      exists students_after raw_after,
        Spec(m, students, __return) &&
        Permutation(students, students_after) &&
        Zlength(raw_after) == 2 * n &&
        (forall i, (0 <= i && i < n) =>
          (raw_after[2 * i] == fst(students_after[i]) &&
           raw_after[2 * i + 1] == snd(students_after[i]))) &&
        IntArray::full(a, 2 * n, raw_after)
*/

{
    (void)m;
    long long *total = calloc((size_t)n + 1, sizeof(*total))
        ;
    qsort(a, (size_t)n, sizeof(*a), cmp_candidate)
        ;
    
    for (int i = 0; i < n;)
    {
        int j = i;
        long long prefix = 0;
        
        while (j < n && ((int *)a)[2 * j] == ((int *)a)[2 * i])
        {
            prefix += ((int *)a)[2 * j + 1];
            ++j;
            if (prefix > 0)
                total[j - i] += prefix;
        }
        i = j;
    }
    long long answer = 0;
    
    for (int k = 1; k <= n; ++k)
        if (total[k] > answer)
            answer = total[k];
    free(total) ;
    return answer;
}

// int main(void)
// {
//     int n, m; if (scanf("%d %d", &n, &m) != 2) return 0;
//     Candidate *a = malloc((size_t)n * sizeof(*a));
//     for (int i = 0; i < n; ++i) scanf("%d %d", &a[i].subject, &a[i].skill);
//     printf("%lld\n", solver(a, n, m)); free(a);
//     return 0;
// }
