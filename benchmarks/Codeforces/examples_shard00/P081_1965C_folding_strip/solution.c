/* Codeforces 1965/C - Folding Strip */
#include <stdio.h>
#include <stdlib.h>
static int solver(int n,const char*s){int cur=0,mn=0,mx=0;for(int i=0;i<n;++i){if(((cur&1)==0)==(s[i]=='1'))++cur;else --cur;if(cur<mn)mn=cur;if(cur>mx)mx=cur;}return mx-mn;}
int main(void){int t;scanf("%d",&t);while(t--){int n;char*s;scanf("%d",&n);s=malloc((size_t)n+1);scanf("%s",s);printf("%d\n",solver(n,s));free(s);}return 0;}
