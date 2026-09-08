/* Codeforces 132/C - Logo Turtle */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define AT(a,c,d,p) (a)[((c)*2+(d))*W+(p)]

static int solver(const char*s,int changes){int len=(int)strlen(s),W=2*len+1,O=len;unsigned char*dp=calloc((size_t)(changes+1)*2*W,1),*ndp=calloc((size_t)(changes+1)*2*W,1);
    AT(dp,0,0,O)=1;for(int i=0;i<len;++i){memset(ndp,0,(size_t)(changes+1)*2*W);for(int c=0;c<=changes;++c)for(int dir=0;dir<2;++dir)for(int pos=0;pos<W;++pos)if(AT(dp,c,dir,pos)){for(int flip=0;flip<=1;++flip){if(c+flip>changes)continue;char cmd=s[i];if(flip)cmd=cmd=='T'?'F':'T';int nd=dir,np=pos;if(cmd=='T')nd^=1;else np+=dir?-1:1;if(np>=0&&np<W)AT(ndp,c+flip,nd,np)=1;}}unsigned char*tmp=dp;dp=ndp;ndp=tmp;}
    int ans=0;for(int c=0;c<=changes;++c)if(((changes-c)&1)==0)for(int d=0;d<2;++d)for(int p=0;p<W;++p)if(AT(dp,c,d,p)){int x=abs(p-O);if(x>ans)ans=x;}free(dp);free(ndp);return ans;}
int main(void){char s[105];int changes;if(scanf("%104s %d",s,&changes)!=2)return 0;printf("%d\n",solver(s,changes));return 0;}
