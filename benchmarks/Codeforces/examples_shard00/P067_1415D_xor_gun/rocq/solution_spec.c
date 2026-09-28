/* Codeforces 1415/D - XOR-gun */
// #include <stdio.h>
// #include <limits.h>
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (NoEqualBitTriplePrefix : list Z -> Z -> Prop)
      (BitScanState : Z -> Z -> Z -> Prop)
      (PrefixXorTable : list Z -> list Z -> Z -> Prop)
      (BruteSearchState : list Z -> Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/

static int solver(const int *a, int n) 
/*@ With (values : list Z)
    Require
      2 <= Zlength(values) && Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 1000000000)) &&
      (forall i, (0 <= i && i + 1 < Zlength(values)) => values[i] <= values[i + 1]) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) && IntArray::full(a, n, values)
*/
{
    
    for (int i = 1; i + 1 < n; ++i)
    {
        int x = a[i - 1], y = a[i], z = a[i + 1], bx = 0, by_count = 0, bz = 0;
        
        while (x > 1)
        {
            x = x >> 1;
            ++bx;
        }
        
        while (y > 1)
        {
            y = y >> 1;
            ++by_count;
        }
        
        while (z > 1)
        {
            z = z >> 1;
            ++bz;
        }
        if (bx == by_count && by_count == bz)
            return 1;
    }
    if (n > 60)
        return 1;
    int pre[64] = {0};
    
    for (int i = 0; i < n; ++i)
        pre[i + 1] = pre[i] ^ a[i];
    int ans = 2147483647;
    
    for (int l = 0; l < n; ++l)
        
        for (int mid = l; mid + 1 < n; ++mid)
            
            for (int r = mid + 1; r < n; ++r)
                if ((pre[mid + 1] ^ pre[l]) > (pre[r + 1] ^ pre[mid + 1]) && r - l - 1 < ans)
                    ans = r - l - 1;
    return ans == 2147483647 ? -1 : ans;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     int a[100005];
//     for (int i = 0; i < n; ++i)
//         scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n));
//     return 0;
// }
