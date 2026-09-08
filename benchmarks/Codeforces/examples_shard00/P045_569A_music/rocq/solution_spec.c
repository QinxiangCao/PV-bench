/* Codeforces 569/A - Music */
// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P045_569A_music.rocq.spec_lib */

static int solver(long long t, long long s,
                  long long q) 

/*@
    Require
      2 <= q && q <= 10000 &&
      1 <= s && s < t &&
      t <= 100000
    Ensure
      Spec(t, s, q, __return)
*/

{
    int starts = 0;
    
    while (s < t)
    {
        s *= q;
        ++starts;
    }
    return starts;
}

// int main(void)
// {
//     long long t, s, q; if (scanf("%lld %lld %lld", &t, &s, &q) != 3) return 0;
//     printf("%d\n", solver(t, s, q));
//     return 0;
// }
