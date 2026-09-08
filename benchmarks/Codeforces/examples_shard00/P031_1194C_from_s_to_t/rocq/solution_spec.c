/* Codeforces 1194/C - From S To T */
// #include <stdio.h>
#include "string.h"

/*@ Extern Coq
      (Spec : list Z -> list Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P031_1194C_from_s_to_t.rocq.spec_lib */

static int solver(const char *s, const char *t, const char *p)

/*@ With (source target pool : list Z)
    Require
      1 <= Zlength(source) && Zlength(source) <= 100 &&
      1 <= Zlength(target) && Zlength(target) <= 100 &&
      1 <= Zlength(pool) && Zlength(pool) <= 100 &&
      (forall idx, (0 <= idx && idx < Zlength(source)) =>
        (97 <= source[idx] && source[idx] <= 122)) &&
      (forall idx, (0 <= idx && idx < Zlength(target)) =>
        (97 <= target[idx] && target[idx] <= 122)) &&
      (forall idx, (0 <= idx && idx < Zlength(pool)) =>
        (97 <= pool[idx] && pool[idx] <= 122)) &&
      CharArray::full(s, Zlength(source) + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, Zlength(source) + 1, 105) *
      CharArray::full(t, Zlength(target) + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, Zlength(target) + 1, 105) *
      CharArray::full(p, Zlength(pool) + 1, app(pool, cons(0, nil))) *
      CharArray::undef_seg(p, Zlength(pool) + 1, 105)
    Ensure
      Spec(source, target, pool, __return) &&
      CharArray::full(s, Zlength(source) + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, Zlength(source) + 1, 105) *
      CharArray::full(t, Zlength(target) + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, Zlength(target) + 1, 105) *
      CharArray::full(p, Zlength(pool) + 1, app(pool, cons(0, nil))) *
      CharArray::undef_seg(p, Zlength(pool) + 1, 105)
*/

{
    int i = 0, cnt[26] = {0};
    
    for (int j = 0; t[j]; ++j) if (s[i]) {
        
        if (s[i] == t[j]) ++i;
    }
    if (s[i])
        
        return 0;

    for (i = 0; s[i]; ++i)
        
        ++cnt[s[i] - 'a'];
    
    for (i = 0; p[i]; ++i)
        
        ++cnt[p[i] - 'a'];
    
    for (i = 0; t[i]; ++i) {
        
        cnt[t[i] - 'a'] = cnt[t[i] - 'a'] - 1;
        if (cnt[t[i] - 'a'] < 0)
        
        return 0;
    }
    
    return 1;
}

// int main(void)
// {
//     int q; scanf("%d", &q);
//     while (q--) {
//         char s[105], t[105], p[105]; scanf("%104s %104s %104s", s, t, p);
//         puts(solver(s, t, p) ? "YES" : "NO");
//     }
//     return 0;
// }
