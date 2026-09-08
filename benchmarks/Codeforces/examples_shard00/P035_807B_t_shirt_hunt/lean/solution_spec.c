/*@ Import Lean
import Codeforces.examples_shard00.P035_807B_t_shirt_hunt.lean.spec_lib
open scoped SimpleC
*/

/* Codeforces 807/B - T-Shirt Hunt */
// #include <stdio.h>

static int wins(int place, int score)

{
    int z = (score / 50) % 475;

    for (int i = 0; i < 25; ++i) {
        z = (z * 96 + 42) % 475;
        if (z + 26 == place) return 1;
    }
    return 0;
}

/*@ Extern Coq
      (Pre : Z -> Z -> Z -> Prop)
      (Spec : Z -> Z -> Z -> Z -> Prop)
*/
static int solver(int p, int x, int y)

/*@
    Require
      26 <= p && p <= 500 &&
      1 <= y && y <= x &&
      x <= 20000 &&
      Pre(p, x, y)
    Ensure
      Spec(p, x, y, __return)
*/

{
    int score = y;

    while ((score - x) % 50 != 0) ++score;

    while (!wins(p, score)) {

        score += 50;
    }

    return score <= x ? 0 : (score - x + 99) / 100;
}

// int main(void)
// {
//     int p, x, y; if (scanf("%d %d %d", &p, &x, &y) != 3) return 0;
//     printf("%d\n", solver(p, x, y));
//     return 0;
// }
