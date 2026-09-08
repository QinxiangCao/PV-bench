/* Codeforces 1393/C - Pinkie Pie Eats Patty-cakes */
#include <stdio.h>
#include <stdlib.h>

static int solver(const int*a,int n)
{int *cnt=calloc((size_t)n+1,sizeof(*cnt));int mx=0,c=0;for(int i=0;i<n;++i)++cnt[a[i]];
 for(int i=1;i<=n;++i)if(cnt[i]>mx){mx=cnt[i];c=1;}else if(cnt[i]==mx)++c;
 int ans=(n-c)/(mx-1)-1;free(cnt);return ans;}

int main(void)
{
    int t;scanf("%d",&t);while(t--){int n;scanf("%d",&n);int*a=malloc((size_t)n*sizeof(*a));
        for(int i=0;i<n;++i)scanf("%d",&a[i]);printf("%d\n",solver(a,n));free(a);
    }return 0;
}
