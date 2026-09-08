/* Codeforces 245/B - Internet Address */
// #include <stdio.h>
#include "string.h"

/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> list Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Extern Coq
      (CharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P022_245B_internet_address.rocq.spec_lib */

static void solver(const char *s,
                   char *out) 

/*@ With (plain : list Z)
    Require
      1 <= Zlength(plain) && Zlength(plain) <= 50 &&
      (forall i, (0 <= i && i < Zlength(plain)) => (97 <= plain[i] && plain[i] <= 122)) &&
      Pre(plain) &&
      CharArray::full(s, Zlength(plain) + 1, app(plain, cons(0, nil))) *
      CharArray::undef_full(out, 72)
    Ensure
      exists address,
        Spec(plain, address) &&
        CharArray::full(s, Zlength(plain) + 1, app(plain, cons(0, nil))) *
        CharArray::full(out, Zlength(address) + 1, app(address, cons(0, nil))) *
        CharArray::undef_seg(out, Zlength(address) + 1, 72)
*/

{
    
    int n = (int)strlen(s) , p = s[0] == 'h' ? 4 : 3, ru = -1, k = 0;
    
    for (int i = p + 1; i + 1 < n; ++i)
        if (s[i] == 'r' && s[i + 1] == 'u')
        {
            ru = i;
            break;
        }

    for (int i = 0; i < p; ++i)
    {
        out[k] = s[i];
        k++;
    }
    out[k] = ':';
    k++;
    out[k] = '/';
    k++;
    out[k] = '/';
    k++;

    for (int i = p; i < ru; ++i)
    {
        out[k] = s[i];
        k++;
    }
    out[k] = '.';
    k++;
    out[k] = 'r';
    k++;
    out[k] = 'u';
    k++;
    
    if (ru + 2 < n)
    {
        out[k] = '/';
        k++;
        
        for (int i = ru + 2; i < n; ++i)
        {
            out[k] = s[i];
            k++;
        }
    }
    
    out[k] = '\0';
}

// int main(void)
// {
//     char s[64], out[72];
//     if (scanf("%63s", s) != 1) return 0;
//     solver(s, out); puts(out);
//     return 0;
// }
