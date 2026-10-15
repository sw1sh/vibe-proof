/* Right diagonals R_j of rule 30 as bitsets; least periods e_j, a_j (of g_j = R_{j-1}|R_{j-2}), S_j. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
static int gb(const u64*v,u64 t){return (v[t>>6]>>(t&63))&1;}
/* least period (power of 2) of v, known to be periodic with period len (len power of 2, v stored with 2*len bits) */
static u64 lp(const u64*v,u64 len){
  for(u64 p=1;p<len;p*=2){int ok=1;
    for(u64 t=0;t<len&&ok;t++) if(gb(v,t)!=gb(v,t+p)) ok=0;
    if(ok) return p;}
  return len;}
int main(int argc,char**argv){
  int J=atoi(argv[1]); int LOG=atoi(argv[2]);
  u64 N=(u64)1<<LOG; u64 W=N/64;
  u64 **R=malloc(sizeof(u64*)*(J+1));
  for(int j=0;j<=J;j++){R[j]=calloc(W,8);}
  memset(R[0],0xff,W*8);
  int e[200],a[200],S[200];
  e[0]=0;
  for(int j=1;j<=J;j++){
    u64 x=0; u64 *c=R[j];
    for(u64 t=0;t<N;t++){
      if(x) c[t>>6]|=(u64)1<<(t&63);
      int g=gb(R[j-1],t)|(j>=2?gb(R[j-2],t):0);
      x^=g;
    }
    /* periods: need period*2 <= N */
    u64 Lg=1; /* g period */
    /* compute g into temp */
    u64*g=calloc(W,8);

    for(u64 k=0;k<W;k++) g[k]=R[j-1][k]|(j>=2?R[j-2][k]:0);
    u64 maxp=N/2;
    u64 pg=lp(g,maxp); u64 pr=lp(c,maxp);
    int par=0; for(u64 t=0;t<pg;t++) par^=gb(g,t);
    a[j]=__builtin_ctzll(pg); e[j]=__builtin_ctzll(pr); S[j]=par;
    printf("j=%d e=%d a=%d S=%d  e-a-S=%d  a-e_{j-1}=%d\n",j,e[j],a[j],S[j],e[j]-a[j]-S[j],a[j]-e[j-1]);
    free(g);
    if((u64)1<<(e[j]+1) > maxp){printf("stop: period too large for N\n");break;}
  }
  return 0;}
