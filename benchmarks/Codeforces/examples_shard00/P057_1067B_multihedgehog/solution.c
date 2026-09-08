/* Codeforces 1067/B - Multihedgehog */
#include <stdio.h>
#include <stdlib.h>

static int n,*head,*to,*nxt,*deg;
static int bfs(int src,int*parent,int*dist){int*q=malloc((size_t)n*sizeof(*q)),l=0,r=0;q[r++]=src;for(int i=0;i<n;++i){dist[i]=-1;parent[i]=-1;}dist[src]=0;int far=src;while(l<r){int v=q[l++];if(dist[v]>dist[far])far=v;for(int e=head[v];e!=-1;e=nxt[e])if(dist[to[e]]<0){dist[to[e]]=dist[v]+1;parent[to[e]]=v;q[r++]=to[e];}}free(q);return far;}
static int solver(int nn,long long k,const int*eu,const int*ev){n=nn;head=malloc((size_t)n*sizeof(*head));deg=calloc((size_t)n,sizeof(*deg));to=malloc((size_t)(2*n-2)*sizeof(*to));nxt=malloc((size_t)(2*n-2)*sizeof(*nxt));for(int i=0;i<n;++i)head[i]=-1;int ec=0;for(int i=0;i+1<n;++i){int u=eu[i],v=ev[i];to[ec]=v;nxt[ec]=head[u];head[u]=ec++;to[ec]=u;nxt[ec]=head[v];head[v]=ec++;++deg[u];++deg[v];}
 int*p=malloc((size_t)n*sizeof(*p)),*d=malloc((size_t)n*sizeof(*d)),ok=1;int a=bfs(0,p,d),b=bfs(a,p,d);if((long long)d[b]!=2*k)ok=0;int center=b;for(long long i=0;ok&&i<k;++i)center=p[center];if(ok)bfs(center,p,d);for(int v=0;ok&&v<n;++v)if(d[v]>k||(d[v]==k&&deg[v]!=1)||(d[v]<k&&((v==center&&deg[v]<3)||(v!=center&&deg[v]<4))))ok=0;
 free(head);free(to);free(nxt);free(deg);free(p);free(d);return ok;}
int main(void){long long k;if(scanf("%d %lld",&n,&k)!=2)return 0;int*eu=malloc((size_t)(n-1)*sizeof(*eu)),*ev=malloc((size_t)(n-1)*sizeof(*ev));for(int i=0;i+1<n;++i){scanf("%d %d",&eu[i],&ev[i]);--eu[i];--ev[i];}puts(solver(n,k,eu,ev)?"Yes":"No");free(eu);free(ev);return 0;}
