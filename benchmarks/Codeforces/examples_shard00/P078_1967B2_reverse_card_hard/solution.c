/* Codeforces 1967/B2 - Reverse Card (Hard Version) */
#include <stdio.h>
static int gcd_int(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
static long long solver(int n,int m){long long ans=0;for(int p=1;(long long)p*p<n;++p)for(int q=1;(long long)q*q<m;++q)if(gcd_int(p,q)==1){int lim=n/p<m/q?n/p:m/q;ans+=lim/(p+q);}return ans;}
int main(void){int t;scanf("%d",&t);while(t--){int n,m;scanf("%d %d",&n,&m);printf("%lld\n",solver(n,m));}return 0;}
