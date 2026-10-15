/* Right half driven by an arbitrary center sequence c': diagonals R'_j on [j, inf):
   R'_j(j) = c'(j), R'_j(t+1) = R'_j(t) ^ (R'_{j-1}(t) | R'_{j-2}(t)),  R'_0 = 1, R'_1(t) = ... (from c'(1)).
   Arrays store R'_j(t) for t in [0, N) with entries t < j meaningless (we compute tails only).
   Report tail least period exponent of each diagonal (period checked on [j, N)), and check the
   light-cone consistency of the periodic backward extension: Rext_j(t) = R'_j(t + k p) for t < j. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static int gb(const u64*v,u64 t){return (v[t>>6]>>(t&63))&1;}
static void sb(u64*v,u64 t,int b){ if(b) v[t>>6]|=(u64)1<<(t&63); else v[t>>6]&=~((u64)1<<(t&63)); }
int main(int argc,char**argv){
  int J=atoi(argv[1]); int LOG=atoi(argv[2]); const char*mode=argv[3]; const char*w=argv[4]; int T=atoi(argv[5]);
  u64 N=(u64)1<<LOG, W=N/64;
  /* true center column for prefix: compute via true right diagonals? simpler: read from file */
  unsigned char *cc=malloc(J+2);
  FILE*f=fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin","rb");
  unsigned char buf[64]; fread(buf,1,64,f); fclose(f);
  int P=strlen(w);
  for(int t=0;t<=J;t++){
    int truebit=(buf[t>>3]>>(7-(t&7)))&1;
    if(strcmp(mode,"true")==0||t<T) cc[t]=truebit; else cc[t]=w[(t-T)%P]-'0';
  }
  u64**R=malloc(sizeof(u64*)*(J+1));
  for(int j=0;j<=J;j++) R[j]=calloc(W,8);
  memset(R[0],0xff,W*8);
  int prevE=0;
  for(int j=1;j<=J;j++){
    int x=cc[j];
    for(u64 t=j;t<N;t++){
      sb(R[j],t,x);
      int g=gb(R[j-1],t)|(j>=2?gb(R[j-2],t):0);
      x^=g;
    }
    /* tail least period: smallest power of 2 p with R(t+p)=R(t) for t in [j, N-p), require N-p-j >= 2p */
    u64 p=1; int found=0;
    for(;p*4+j<N;p*=2){ int ok=1; for(u64 t=j;t+p<N&&ok;t++) if(gb(R[j],t)!=gb(R[j],t+p)) ok=0; if(ok){found=1;break;} }
    if(!found){printf("j=%d: period > %llu, stop\n",j,(unsigned long long)p);break;}
    int E=__builtin_ctzll(p);
    /* backward extension check: for t<j, Rext(t)=R(t+kp) with t+kp>=j */
    int bad0=0,badcone=0,badedge=0;
    u64 k=(j+p-1)/p; if(k==0)k=1;
    for(u64 t=0;t<(u64)j;t++){
      u64 tt=t+k*p; while(tt<(u64)j) tt+=p;
      int v=gb(R[j],tt);
      if(2*t<(u64)j && v) badcone++;
      if(t==(u64)((j+1)/2) && !v) badedge=1;
    }
    printf("j=%2d c'=%d tailE=%2d step=%2d  cone-violations=%d edge-violation=%d\n",j,cc[j],E,E-prevE,badcone,badedge);
    prevE=E;
  }
  return 0;}
