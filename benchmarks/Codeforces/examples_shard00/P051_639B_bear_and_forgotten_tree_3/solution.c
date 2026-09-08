/* Codeforces 639/B - Bear and Forgotten Tree 3 */
#include <stdio.h>

static int solver(int n, int d, int h, int *eu, int *ev)
{
    if(d>2*h || d<h || (d==1 && n>2)) return -1;
    int count=0,next=2,last=1;
    for(int i=0;i<h;++i){eu[count]=last;ev[count++]=next;last=next++;}
    last=1;for(int i=0;i<d-h;++i){eu[count]=last;ev[count++]=next;last=next++;}
    int attach=(d==h)?2:1;while(next<=n){eu[count]=attach;ev[count++]=next++;}
    return count;
}

int main(void)
{
    int n,d,h; if(scanf("%d %d %d",&n,&d,&h)!=3)return 0;
    int eu[100000],ev[100000],count=solver(n,d,h,eu,ev);if(count<0){puts("-1");return 0;}
    for(int i=0;i<count;++i)printf("%d %d\n",eu[i],ev[i]);
    return 0;
}
