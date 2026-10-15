/* For each right diagonal R_j: e_j, S_j, weight (#ones over a least period), its parity W_j,
   center bit c(j)=R_j(j), and R_j(2^{e_j-1}+j) (half-period partner of the center). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
static int gb(const u64*v,u64 t){return (v[t>>6]>>(t&63))&1;}
int main(int argc,char**argv){
  int J=atoi(argv[1]); int LOG=atoi(argv[2]);
  u64 N=(u64)1<<LOG; u64 W=N/64;
  u64 **R=malloc(sizeof(u64*)*(J+1));
  for(int j=0;j<=J;j++){R[j]=calloc(W,8);}
  memset(R[0],0xff,W*8);
  int e[200]; e[0]=0;
  for(int j=1;j<=J;j++){
    u64 x=0; u64 *c=R[j];
    for(u64 t=0;t<N;t++){
      if(x) c[t>>6]|=(u64)1<<(t&63);
      int g=gb(R[j-1],t)|(j>=2?gb(R[j-2],t):0);
      x^=g;
    }
    u64 p=1; while(p<N/2){int ok=1; for(u64 t=0;t<N/2&&ok;t++) if(gb(c,t)!=gb(c,t+p)) ok=0; if(ok)break; p*=2;}
    e[j]=__builtin_ctzll(p);
    if(2*p>N){printf("stop\n");break;}
    long wt=0; for(u64 t=0;t<p;t++) wt+=gb(c,t);
    int S=e[j]-e[j-1];
    int cj=gb(c,j);
    int half = e[j]>=1 ? gb(c,(j+p/2)%p) : -1;
    printf("j=%2d e=%2d S=%d weight=%8ld (frac %.4f) W=%ld c(j)=%d R_j(j+p/2)=%d\n",j,e[j],S,wt,(double)wt/p,wt&1,cj,half);
  }
  return 0;}
