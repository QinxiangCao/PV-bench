/* Codeforces 1989/E - Distance to Different */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;
void *calloc(size_t nmemb, size_t size)
/*@ Require 0 <= nmemb && size == sizeof(long long)
    Ensure __return != 0 &&
           Int64Array::full(__return, nmemb, repeat_Z(0, nmemb))
*/;
void free(void *ptr)
/*@ Require exists values cap, Int64Array::full(ptr, cap, values)
    Ensure emp
*/;
#define MOD 998244353LL
#define AT(a, i, j) (a)[(size_t)(i) * W + (j)]
/*@ Extern Coq
      (Zmin : Z -> Z -> Z)
      (Spec : Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (P082InitState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082ColumnsState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082ColumnProgress : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082FinalValue : Z -> Z -> list Z -> Z -> Prop)
*/
/*@ Extern Coq
      (P082SemanticInit : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082SemanticColumns : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082SemanticProgress : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
*/
static long long solver(int n,
                        int k) 
/*@
    Require
      2 <= n && n <= 200000 &&
      2 <= k && k <= Zmin(n, 10)
    Ensure
      Spec(n, k, __return)
*/
{
    int W = k + 1;
    long long *dp = calloc((size_t)(n + 1) * W, sizeof(*dp)),
              *pref = calloc((size_t)(n + 1) * W, sizeof(*pref));
    
    for (int i = 1; i <= n; ++i)
    {
        
        AT(dp, i, 1) = 1;
        AT(pref, i, 1) = (AT(pref, i - 1, 1) + 1) % MOD;
    }
    
    for (int j = 2; j <= k; ++j)
    {
        
        for (int i = 1; i <= n; ++i)
        {
            
            long long val = AT(pref, i - 1, j - 1);
            if (i >= 3)
            {
                
                val -= AT(dp, i - 2, j - 1);
            }
            if (j == k)
            {
                
                val += AT(pref, i - 1, k);
                if (i >= 3)
                {
                    
                    val -= AT(dp, i - 2, k);
                }
            }
            
            AT(dp, i, j) = (val % MOD + MOD) % MOD;
            
            AT(pref, i, j) = (AT(pref, i - 1, j) + AT(dp, i, j)) % MOD;
        }
    }
    
    long long ans = AT(dp, n, k);
    if (n >= 2)
    {
        
        ans = (ans + AT(dp, n - 2, k - 1) + AT(dp, n - 2, k)) % MOD;
    }
    
    free(dp);
    free(pref);
    return ans;
}
// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     printf("%lld\n", solver(n, k));
//     return 0;
// }
