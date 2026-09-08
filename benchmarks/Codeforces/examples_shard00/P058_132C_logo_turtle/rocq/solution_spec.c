/* Codeforces 132/C - Logo Turtle */
// #include <stdio.h>
#include "string.h"
// #include <stdlib.h>

typedef unsigned long size_t;

#define AT(a, c, d, p) (a)[((c) * 2 + (d)) * W + (p)]

/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P058_132C_logo_turtle.rocq.spec_lib */

void *calloc(unsigned long nmemb, unsigned long size)
    /*@ calloc_uchar
    With (cells : Z)
    Require
      0 <= cells && cells <= INT_MAX &&
      nmemb == cells && size == 1
    Ensure
      __return != 0 &&
      UCharArray::full(__return, cells, repeat_Z(0, cells))
*/
    ;

char *memset(char *s, int c, int n)
    /*@ memset_uchar_zero
    With (old : list Z)
    Require
      0 <= n && n <= INT_MAX &&
      c == 0 && Zlength(old) == n &&
      UCharArray::full(s, n, old)
    Ensure
      __return == s &&
      UCharArray::full(s, n, repeat_Z(0, n))
*/
    ;

int strlen(char *s)
    /*@ strlen_logo_commands
    With (text : list Z)
    Require
      0 <= Zlength(text) && Zlength(text) < INT_MAX &&
      (forall i, (0 <= i && i < Zlength(text)) =>
        ((text[i] == 70) || (text[i] == 84))) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    Ensure
      __return == Zlength(text) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
*/
    ;

int abs(int value)
    /*@ abs_logo_position
    Require
      INT_MIN < value && value <= INT_MAX
    Ensure
      ((0 <= value && __return == value) ||
       (value < 0 && __return == -value))
*/
    ;

void free(void *ptr)
    /*@ free_uchar
    Require
      exists cells values,
        UCharArray::full(ptr, cells, values)
    Ensure emp
*/
    ;

static int solver(const char *s, int changes) 

/*@ With (n : Z)
             (commands : list Z)
    Require
      1 <= Zlength(commands) && Zlength(commands) <= 100 &&
      1 <= n && n <= 50 &&
      (forall i, (0 <= i && i < Zlength(commands)) =>
        ((commands[i] == 70) || (commands[i] == 84))) &&
      changes == n &&
      CharArray::full(s, Zlength(commands) + 1, app(commands, cons(0, nil)))
    Ensure
      Spec(n, commands, __return) &&
      CharArray::full(s, Zlength(commands) + 1, app(commands, cons(0, nil)))
*/

{
    int len = (int)strlen(s)
        ;
    int W = 2 * len + 1;
    int O = len;
    unsigned char *dp = calloc((size_t)(changes + 1) * 2 * W, 1)
        ;
    unsigned char *ndp = calloc((size_t)(changes + 1) * 2 * W, 1)
        ;

    AT(dp, 0, 0, O) = 1;
    
    for (int i = 0; i < len; ++i) {
        memset((char *)ndp, 0, (int)((size_t)(changes + 1) * 2 * W))
            ;
        
        for (int c = 0; c <= changes; ++c) {
            
            for (int dir = 0; dir < 2; ++dir) {
                
                for (int pos = 0; pos < W; ++pos) {
                    
                    if (AT(dp, c, dir, pos)) {
                        
                        for (int flip = 0; flip <= 1; ++flip) {
                            if (c + flip > changes) {
                                continue;
                            }
                            char cmd = s[i];
                            if (flip) {
                                cmd = cmd == 'T' ? 'F' : 'T';
                            }
                            int nd = dir;
                            int np = pos;
                            if (cmd == 'T') {
                                nd ^= 1;
                            } else {
                                np += dir ? -1 : 1;
                            }
                            
                            if (np >= 0 && np < W) {
                                
                                AT(ndp, c + flip, nd, np) = 1;
                            }
                        }
                    }
                }
            }
        }
        
        unsigned char *tmp = dp;
        dp = ndp;
        ndp = tmp;
    }

    int ans = 0;
    
    for (int c = 0; c <= changes; ++c) {
        if (((changes - c) & 1) == 0) {
            
            for (int d = 0; d < 2; ++d) {
                
                for (int p = 0; p < W; ++p) {
                    
                    if (AT(dp, c, d, p)) {
                        int x = abs(p - O)
                            ;
                        if (x > ans) {
                            ans = x;
                        }
                    }
                }
            }
        }
    }

    free(dp) ;
    free(ndp) ;
    return ans;
}

// int main(void)
// {
//     char s[105];
//     int changes;
//     if (scanf("%104s %d", s, &changes) != 2) {
//         return 0;
//     }
//     printf("%d\n", solver(s, changes));
//     return 0;
// }
