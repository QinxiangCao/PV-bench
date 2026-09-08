/* Codeforces 1146/B - Hate "A" */
// #include <stdio.h>
#include "string.h"

/*@ Extern Coq
      (Spec : list Z -> option (list Z) -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P018_1146B_hate_a.rocq.spec_lib */

static int solver(const char *given, char *out) 

/*@ With (given_data : list Z)
    Require
      1 <= Zlength(given_data) && Zlength(given_data) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(given_data)) => (97 <= given_data[i] && given_data[i] <= 122)) &&
      CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
      CharArray::undef_full(out, 100005)
    Ensure
      CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
      ((__return == 0 && Spec(given_data, None) &&
        CharArray::full(out, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
        CharArray::undef_seg(out, Zlength(given_data) + 1, 100005)) ||
       (exists result,
          __return == 1 && Spec(given_data, Some(result)) &&
          CharArray::full(out, Zlength(result) + 1, app(result, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(result) + 1, 100005)))
*/

{
    char stripped[100005];
    
    strcpy(out, given) ;
    int n = (int)strlen(out) , k = 0;
    
    for (int i = 0; i < n; ++i)
        if (out[i] != 'a')
        {
            stripped[k] = out[i];
            ++k;
        }
    if (k & 1)
    {
        
        return 0;
    }
    int suffix = k / 2, prefix = n - suffix;
    
    for (int i = prefix; i < n; ++i)
        if (out[i] == 'a')
        {
            
            return 0;
        }
    
    for (int i = 0; i < suffix; ++i)
        if (stripped[i] != out[prefix + i])
        {
            
            return 0;
        }
    out[prefix] = '\0';
    
    return 1;
}

// int main(void)
// {
//     static char t[100005], out[100005];
//     if (scanf("%100004s", t) != 1) return 0;
//     puts(solver(t, out) ? out : ":(");
//     return 0;
// }
