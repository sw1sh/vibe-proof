// Independent re-implementation: right half (p >= 1) of rule 30 driven by c = w^inf (phase ph) from time 0.
// mode 0: random finite right-half start of width initw (trials, seed)
// mode 1: start = actual single-seed rule-30 right half at time T, for T = Tmin..Tmax, all phases
// Reports masked periodicity (col1 at zeros of c, period multiple of |w|, checked on [steps/2, steps))
// and full periodicity (independent search), plus the latest violation time for the masked period.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 2048
static uint64_t row[MAXW], nrow[MAXW];
static unsigned char *col1;
static uint64_t rs = 0x243F6A8885A308D3ULL;
static uint64_t xr(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int nw;
static void step(int ct){
  for (int k=0;k<nw;k++){
    uint64_t L = (row[k] << 1) | (k ? row[k-1] >> 63 : (uint64_t)ct);
    uint64_t R = (row[k] >> 1) | (k+1<nw ? row[k+1] << 63 : 0);
    nrow[k] = L ^ (row[k] | R);
  }
  memcpy(row,nrow,sizeof(uint64_t)*nw);
}
static int masked_Q(const char*w,int P,int ph,int steps,int full){
  int start=steps/2;
  for(int m=1;m<=64;m++){ int Q=P*m; if(start+Q>=steps) break;
    int ok=1;
    for(int t=start;t+Q<steps;t++){ int ct=w[(t+ph)%P]-'0'; if((full||ct==0) && col1[t]!=col1[t+Q]){ok=0;break;} }
    if(ok) return Q; }
  return 0;
}
int main(int argc,char**argv){
  const char*w=argv[1]; int P=strlen(w); int steps=atoi(argv[2]); int mode=atoi(argv[3]);
  col1 = malloc(steps+8);
  if(mode==0){
    int trials=atoi(argv[4]), initw=atoi(argv[5]); rs ^= (uint64_t)atoll(argv[6])*0x9E3779B97F4A7C15ULL;
    nw=(initw+steps)/64+2; if(nw>MAXW){fprintf(stderr,"wide\n");return 1;}
    int nm=0,nf=0,nmf=0;
    for(int tr=0;tr<trials;tr++){
      memset(row,0,sizeof(uint64_t)*nw);
      for(int i=0;i<initw;i++) if(xr()&1) row[i>>6]|=1ULL<<(i&63);
      for(int t=0;t<steps;t++){ col1[t]=row[0]&1; step(w[t%P]-'0'); }
      int qm=masked_Q(w,P,0,steps,0), qf=masked_Q(w,P,0,steps,1);
      if(qm) nm++; if(qf) nf++; if(qm&&qf) nmf++;
      if(argc>7) printf("trial %d masked Q=%d full Q=%d\n",tr,qm,qf);
    }
    printf("%s mode0 steps=%d initw=%d: masked-periodic %d/%d, full-periodic %d/%d\n",w,steps,initw,nm,trials,nf,trials);
  } else {
    int Tmin=atoi(argv[4]), Tmax=atoi(argv[5]);
    int bad=0, tot=0;
    for(int T=Tmin;T<=Tmax;T++) for(int ph=0;ph<P;ph++){
      // actual single-seed pattern at time T: positions -T..T; right half p>=1
      nw=(T+steps)/64+2; if(nw>MAXW){fprintf(stderr,"wide\n");return 1;}
      // simulate full pattern to time T using a separate array (positions offset)
      int Wd=2*T+3; unsigned char *a=calloc(Wd+2,1),*b=calloc(Wd+2,1);
      a[T+1]=1; // index = p + T + 1
      for(int s=0;s<T;s++){ for(int i=1;i<=Wd;i++){ b[i]=a[i-1]^(a[i]|a[i+1]); } unsigned char*tmp=a;a=b;b=tmp; }
      memset(row,0,sizeof(uint64_t)*nw);
      for(int p=1;p<=T;p++) if(a[p+T+1]) row[(p-1)>>6]|=1ULL<<((p-1)&63);
      free(a);free(b);
      for(int t=0;t<steps;t++){ col1[t]=row[0]&1; step(w[(t+ph)%P]-'0'); }
      int qm=masked_Q(w,P,ph,steps,0); tot++;
      if(!qm){ bad++; printf("T=%d phase=%d: masked col1 NOT periodic within horizon\n",T,ph); }
    }
    printf("%s mode1 T=%d..%d steps=%d: not-masked-periodic %d/%d\n",w,Tmin,Tmax,steps,bad,tot);
  }
  return 0;
}
