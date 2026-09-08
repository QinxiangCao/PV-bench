/* Codeforces 1168/A - Increasing by Modulo */
#include <stdio.h>
#include <stdlib.h>

static int n,m,*a;
static int feasible(int x)
{
    int last=0;
    for(int i=0;i<n;++i){
        if(a[i]+x<m){if(a[i]+x<last)return 0;if(a[i]>last)last=a[i];}
        else {int wrapped=(a[i]+x)%m;if(a[i]>last && wrapped<last)last=a[i];}
    }
    return 1;
}
static int solver(int nn,int mm,const int*input)
{
    n=nn;m=mm;a=(int*)input;int lo=0,hi=m-1,ans=hi;
    while(lo<=hi){int mid=(lo+hi)/2;if(feasible(mid)){ans=mid;hi=mid-1;}else lo=mid+1;}
    a=NULL;return ans;
}
int main(void)
{
    if(scanf("%d %d",&n,&m)!=2)return 0;a=malloc((size_t)n*sizeof(*a));for(int i=0;i<n;++i)scanf("%d",&a[i]);
    int*out=a;printf("%d\n",solver(n,m,out));free(out);return 0;
}
