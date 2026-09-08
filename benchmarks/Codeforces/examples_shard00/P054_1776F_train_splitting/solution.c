/* Codeforces 1776/F - Train Splitting */
#include <stdio.h>
#include <stdlib.h>

static int solver(int n,int m,const int*u,const int*v,int*colors)
{int*deg=calloc((size_t)n,sizeof(*deg));for(int i=0;i<m;++i){++deg[u[i]];++deg[v[i]];}
 int pivot=-1;for(int i=0;i<n;++i)if(deg[i]<n-1){pivot=i;break;}
 int kinds;if(pivot>=0){kinds=2;for(int i=0;i<m;++i)colors[i]=(u[i]==pivot||v[i]==pivot)?1:2;}
 else{kinds=3;int first=1;for(int i=0;i<m;++i){if(u[i]==0||v[i]==0){colors[i]=first?1:2;first=0;}else colors[i]=3;}}
 free(deg);return kinds;}

int main(void)
{
    int t;scanf("%d",&t);while(t--){int n,m;scanf("%d %d",&n,&m);int *u=malloc((size_t)m*sizeof(*u)),*v=malloc((size_t)m*sizeof(*v)),*colors=malloc((size_t)m*sizeof(*colors));
        for(int i=0;i<m;++i){scanf("%d %d",&u[i],&v[i]);--u[i];--v[i];}
        printf("%d\n",solver(n,m,u,v,colors));for(int i=0;i<m;++i)printf("%d%c",colors[i],i+1==m?'\n':' ');
        free(colors);free(u);free(v);
    }return 0;
}
