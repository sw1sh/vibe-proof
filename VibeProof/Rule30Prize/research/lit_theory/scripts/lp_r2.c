/* Scan binary radius-2 left-permutive rules f(a,b,c,d,e) = a XOR g(b,c,d,e)
   with g(0000)=0 (quiescent) and g(0001)=1 (left border moves left at speed 2).
   From a single seed, test columns -2..2 for eventual periodicity (period <= PMAX,
   checked on t in [T/2, T)). For rules with an eventually periodic column, test whether
   f agrees with an affine function on all 5-windows occurring in the light cone ("affine on orbit"). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T 512
#define W (4*T+16)
#define OFF (2*T+8)
#define PMAX 64
static unsigned char row[W], nrow[W];
static unsigned char col[5][T];
static unsigned char seen[32];
static int evper(unsigned char *s){
  for(int P=1;P<=PMAX;P++){int ok=1;for(int t=T/2;t+P<T;t++) if(s[t]!=s[t+P]){ok=0;break;} if(ok) return P;}
  return 0;
}
/* is there an affine A(w)=a0^sum ak wk (k=0..4 bits of window) agreeing with f on all seen windows? brute force 64 */
static int affine_on_orbit(unsigned int ftab){
  for(int a=0;a<64;a++){int ok=1;
    for(int w=0;w<32&&ok;w++) if(seen[w]){
      int v=a&1; for(int k=0;k<5;k++) if((a>>(k+1))&1) v^=(w>>k)&1;
      if(v!=((ftab>>w)&1)) ok=0;}
    if(ok) return 1;}
  return 0;
}
int main(int argc,char**argv){
  long nrules=0,nper=0,nnonaff=0;
  for(unsigned int g=0; g<65536; g++){
    /* g index: bits (b,c,d,e) -> idx = b*8+c*4+d*2+e */
    if(g&1) continue;            /* g(0000)=0 */
    if(!((g>>1)&1)) continue;    /* g(0001)=1 */
    nrules++;
    unsigned int ftab=0; /* window w = a*16+b*8+c*4+d*2+e  (a = leftmost x_{i-2}) */
    for(int w=0;w<32;w++){int a=(w>>4)&1; int v=a^((g>>(w&15))&1); if(v) ftab|=1u<<w;}
    memset(row,0,sizeof row); memset(seen,0,sizeof seen); row[OFF]=1;
    for(int t=0;t<T;t++){
      for(int k=0;k<5;k++) col[k][t]=row[OFF-2+k];
      int lo=OFF-2*t-2, hi=OFF+2*t+2;
      for(int i=lo;i<=hi;i++){
        int w=(row[i-2]<<4)|(row[i-1]<<3)|(row[i]<<2)|(row[i+1]<<1)|row[i+2];
        if(t<T-1) seen[w]=1;
        nrow[i]=(ftab>>w)&1;
      }
      memcpy(row+lo,nrow+lo,hi-lo+1);
    }
    int per[5],any=0; for(int k=0;k<5;k++){per[k]=evper(col[k]); if(per[k]) any=1;}
    if(any){ nper++;
      int aff=affine_on_orbit(ftab);
      if(!aff){ nnonaff++;
        printf("g=0x%04x ftab=0x%08x periods(cols -2..2)= %d %d %d %d %d  nonaffine-on-orbit\n",g,ftab,per[0],per[1],per[2],per[3],per[4]);
      }
    }
  }
  fprintf(stderr,"rules=%ld with_periodic_col=%ld nonaffine=%ld\n",nrules,nper,nnonaff);
  return 0;
}
