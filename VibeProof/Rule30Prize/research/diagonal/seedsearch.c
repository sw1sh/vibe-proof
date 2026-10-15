/* Search finite seeds for a column that looks eventually periodic.
   For each seed (bits b_0..b_{w-1} at positions 0..w-1, b_0 = b_{w-1} = 1), run T steps of rule 30,
   record columns p in [-PL, w-1+PR]; test whether column p satisfies x(t+P)=x(t) for all t in [T/2, T-P),
   for some P <= PMAX. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  int W=atoi(argv[1]); int T=atoi(argv[2]); int PMAX=atoi(argv[3]); int PL=atoi(argv[4]);
  int width=2*T+W+10; int off=T+5;
  unsigned char *a=malloc(width),*b=malloc(width);
  int ncol=W+2*PL; unsigned char *col=malloc((size_t)ncol*(T+1));
  long hits=0;
  for(long seed=0; seed < (1L<<(W-2)); seed++){
    memset(a,0,width);
    a[off]=1; a[off+W-1]=1;
    for(int i=1;i<W-1;i++) a[off+i]=(seed>>(i-1))&1;
    int lo=off, hi=off+W-1;
    for(int t=0;t<=T;t++){
      for(int c=0;c<ncol;c++){ int p=off-PL+c; col[(size_t)c*(T+1)+t]=a[p]; }
      if(t==T)break;
      for(int p=lo-1;p<=hi+1;p++) b[p]=a[p-1]^(a[p]|a[p+1]);
      b[lo-2]=0; b[hi+2]=0;
      lo--;hi++;
      unsigned char*tmp=a;a=b;b=tmp;
    }
    for(int c=0;c<ncol;c++){
      unsigned char*x=col+(size_t)c*(T+1);
      for(int P=1;P<=PMAX;P++){
        int ok=1; for(int t=T/2;t+P<=T;t++) if(x[t]!=x[t+P]){ok=0;break;}
        if(ok){ hits++; if(hits<=20) printf("seed=%ld (w=%d) column offset %d: period %d\n",seed,W,c-PL,P); break;}
      }
    }
  }
  printf("W=%d T=%d hits=%ld\n",W,T,hits);
  return 0;}
