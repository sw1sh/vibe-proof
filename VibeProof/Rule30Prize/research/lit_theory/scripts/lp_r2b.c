/* Refine: for radius-2 left-permutive rules (a XOR g(b,c,d,e)), g(0000)=0, g(0001)=1,
   single seed, T steps. Report rules where column 0 (the seed column) is eventually periodic
   (period<=PMAX on [T/2,T)), f is non-affine on the occurring windows, and the orbit is "complex":
   block entropy of the last row (12-blocks inside light cone) >= HMIN, and the row's density in [0.2,0.8]. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define T 1024
#define W (4*T+16)
#define OFF (2*T+8)
#define PMAX 64
#define B 12
static unsigned char row[W], nrow[W];
static unsigned char col[5][T];
static unsigned char seen[32];
static unsigned char blk[1<<B];
static int evper(unsigned char *s){
  for(int P=1;P<=PMAX;P++){int ok=1;for(int t=T/2;t+P<T;t++) if(s[t]!=s[t+P]){ok=0;break;} if(ok) return P;}
  return 0;
}
static int affine_on_orbit(unsigned int ftab){
  for(int a=0;a<64;a++){int ok=1;
    for(int w=0;w<32&&ok;w++) if(seen[w]){
      int v=a&1; for(int k=0;k<5;k++) if((a>>(k+1))&1) v^=(w>>k)&1;
      if(v!=((ftab>>w)&1)) ok=0;}
    if(ok) return 1;}
  return 0;
}
int main(int argc,char**argv){
  double HMIN = argc>1? atof(argv[1]) : 0.7;
  long cnt=0;
  for(unsigned int g=0; g<65536; g++){
    if(g&1) continue; if(!((g>>1)&1)) continue;
    unsigned int ftab=0;
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
    int p0=evper(col[2]);
    if(!p0) continue;
    if(affine_on_orbit(ftab)) continue;
    /* block entropy and density of final row inside [-T, T] (well inside light cone of speed-2 left edge) */
    memset(blk,0,sizeof blk); int nb=0; long ones=0; int L=OFF-T, R=OFF+T;
    for(int i=L;i<=R;i++) ones+=row[i];
    for(int i=L;i+B<=R;i++){int w=0; for(int k=0;k<B;k++) w=(w<<1)|row[i+k]; if(!blk[w]){blk[w]=1;nb++;}}
    double H=log2((double)nb)/B; double dens=(double)ones/(R-L+1);
    if(H>=HMIN && dens>0.2 && dens<0.8){
      int per[5]; for(int k=0;k<5;k++) per[k]=evper(col[k]);
      printf("g=0x%04x ftab=0x%08x H12=%.3f dens=%.3f periods(cols -2..2)= %d %d %d %d %d\n",g,ftab,H,dens,per[0],per[1],per[2],per[3],per[4]);
      cnt++;
    }
  }
  fprintf(stderr,"count=%ld\n",cnt);
  return 0;
}
