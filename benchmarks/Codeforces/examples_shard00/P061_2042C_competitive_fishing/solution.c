/* Codeforces 2042/C - Competitive Fishing */
#include <stdio.h>
#include <stdlib.h>
static int cmp_desc(const void*x,const void*y){int a=*(const int*)x,b=*(const int*)y;return(b>a)-(b<a);}
static int solver(const char*s,int n,long long k){int*gain=malloc((size_t)(n-1)*sizeof(*gain)),sum=s[n-1]=='1'?1:-1;for(int i=n-2;i>=0;--i){gain[i]=sum;sum+=s[i]=='1'?1:-1;}qsort(gain,(size_t)(n-1),sizeof(*gain),cmp_desc);long long cur=0;int ans=-1;for(int i=0;i<n-1;++i){cur+=gain[i];if(cur>=k){ans=i+2;break;}}free(gain);return ans;}
int main(void){int t;scanf("%d",&t);while(t--){int n;long long k;char*s;scanf("%d %lld",&n,&k);s=malloc((size_t)n+1);scanf("%s",s);printf("%d\n",solver(s,n,k));free(s);}return 0;}
