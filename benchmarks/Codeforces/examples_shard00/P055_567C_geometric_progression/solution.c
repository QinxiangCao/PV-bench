/* Codeforces 567/C - Geometric Progression */
#include <stdio.h>
#include <stdlib.h>

static int cmp_ll(const void*x,const void*y){long long a=*(const long long*)x,b=*(const long long*)y;return(a>b)-(a<b);}
static int lower_bound_ll(const long long*a,int n,long long x){int l=0,r=n;while(l<r){int m=(l+r)/2;if(a[m]<x)l=m+1;else r=m;}return l;}
static long long solver(const long long*input,int n,long long k)
{long long*a=malloc((size_t)n*sizeof(*a)),*vals=malloc((size_t)n*sizeof(*vals));for(int i=0;i<n;++i)a[i]=vals[i]=input[i];
 qsort(vals,(size_t)n,sizeof(*vals),cmp_ll);int un=0;for(int i=0;i<n;++i)if(i==0||vals[i]!=vals[i-1])vals[un++]=vals[i];
 long long*left=calloc((size_t)un,sizeof(*left)),*right=calloc((size_t)un,sizeof(*right));for(int i=0;i<n;++i)++right[lower_bound_ll(vals,un,a[i])];long long ans=0;
 for(int i=0;i<n;++i){int ix=lower_bound_ll(vals,un,a[i]);--right[ix];if(a[i]%k==0){long long lo=a[i]/k,hi=a[i]*k;int li=lower_bound_ll(vals,un,lo),ri=lower_bound_ll(vals,un,hi);if(li<un&&vals[li]==lo&&ri<un&&vals[ri]==hi)ans+=left[li]*right[ri];}++left[ix];}
 free(a);free(vals);free(left);free(right);return ans;}
int main(void)
{
    int n;long long k;if(scanf("%d %lld",&n,&k)!=2)return 0;long long*a=malloc((size_t)n*sizeof(*a));
    for(int i=0;i<n;++i)scanf("%lld",&a[i]);printf("%lld\n",solver(a,n,k));free(a);return 0;
}
