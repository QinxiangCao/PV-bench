/* Codeforces 1551/C - Interesting Story */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"

static int cmp_desc(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (b > a) - (b < a);
}

/*@ Extern Coq
      (Spec : list (list Z) -> Z -> Prop)
      (CharPtrArray2::full : Z -> Z -> list (list Z) -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P042_1551C_interesting_story.rocq.spec_lib */
/*@ Extern Coq
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (CharPtrArray2::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (decreasing : list Z -> Prop)
*/
/*@ Extern Coq
      (TotalLength : list (list Z) -> Z)
*/
/*@ include strategies "ptr_array2.strategies" */

void *malloc(unsigned long size)
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

void qsort(int *base, unsigned long nmemb, unsigned long size,
           int (*compar)(const void *, const void *))
    /*@ With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      size == sizeof(int) &&
      IntArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        decreasing(sorted) &&
        Zlength(sorted) == nmemb &&
        IntArray::full(base, nmemb, sorted)
*/
    ;

void free(void *ptr)
    /*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/
    ;

static int solver(char *const *words,
                  int n) 

/*@ With (words_data rows : list (list Z))
    Require
      1 <= Zlength(words_data) && Zlength(words_data) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(words_data)) =>
        0 < Zlength(words_data[i])) &&
      (forall i j,
        (0 <= i && i < Zlength(words_data) &&
         0 <= j && j < Zlength(words_data[i])) =>
          (97 <= Znth(j, Znth(i, words_data, nil), 0) &&
           Znth(j, Znth(i, words_data, nil), 0) <= 101)) &&
      TotalLength(words_data) <= 200000 &&
      n == Zlength(words_data) &&
      Zlength(rows) == n &&
      (forall i, (0 <= i && i < n) =>
        (Znth(i, rows, nil) == c_string(Znth(i, words_data, nil)) &&
         valid_string(Znth(i, words_data, nil)) &&
         string_length(Znth(i, words_data, nil)) < INT_MAX)) &&
      CharPtrArray2::full(words, n, rows)
    Ensure
      Spec(words_data, __return) &&
      CharPtrArray2::full(words, n, rows)
*/

{
    int *score = malloc(5 * n * sizeof(*score))
        ;
    
    for (int i = 0; i < n; ++i)
    {
        
        int len = (int)strlen(words[i])
            ,
            cnt[5] = {0};
        
        for (int j = 0; j < len; ++j)
        {
            
            ++cnt[words[i][j] - 'a'];
        }
        
        for (int c = 0; c < 5; ++c)
        {
            
            score[c * n + i] = 2 * cnt[c] - len;
        }
    }
    
    int answer = 0;
    
    for (int c = 0; c < 5; ++c)
    {
        
        qsort(score + c * n, n, sizeof(*score), cmp_desc);
        
        int sum = 0, take = 0;
        
        while (take < n && sum + score[c * n + take] > 0)
        {
            sum += score[c * n + take];
            ++take;
        }
        
        if (take > answer)
            answer = take;
    }
    free(score) ;
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; scanf("%d", &n); char **words = malloc((size_t)n * sizeof(*words));
//         for (int i = 0; i < n; ++i) { words[i] = malloc(200005); scanf("%200004s", words[i]); }
//         printf("%d\n", solver(words, n));
//         for (int i = 0; i < n; ++i) free(words[i]); free(words);
//     }
//     return 0;
// }
