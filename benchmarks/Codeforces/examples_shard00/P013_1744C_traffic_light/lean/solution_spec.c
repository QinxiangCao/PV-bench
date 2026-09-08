/*@ Import Lean
import Codeforces.examples_shard00.P013_1744C_traffic_light.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 1744/C - Traffic Light */
// #include <stdio.h>
#include "string.h"

/*@ Extern Coq
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
static int solver(const char *s, int n, char c)

/*@ With (lights : list Z)
    Require
      n == Zlength(lights) &&
      1 <= Zlength(lights) && Zlength(lights) <= 200000 &&
      (c == 114 || c == 121 || c == 103) &&
      (forall idx, (0 <= idx && idx < Zlength(lights)) =>
        (lights[idx] == 114 || lights[idx] == 121 || lights[idx] == 103)) &&
      Pre(c, lights) &&
      CharArray::full(s, n + 1, app(lights, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
    Ensure
      Spec(c, lights, __return) &&
      CharArray::full(s, n + 1, app(lights, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
*/

{

    if (c == 'g') return 0;
    int ans = 0, next_green = -1;

    for (int i = 2 * n - 1; i >= 0; --i) {

        char ch = s[i % n];
        if (ch == 'g') next_green = i;
        if (i < n && ch == c && next_green - i > ans) ans = next_green - i;
    }
    return ans;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; char c, s[200005];
//         scanf("%d %c %200004s", &n, &c, s);
//         printf("%d\n", solver(s, n, c));
//     }
//     return 0;
// }
