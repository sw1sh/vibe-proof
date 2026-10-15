/* Independent direct simulation of rule 30 from a single cell, bit-packed.
   Position p in [-T-2, T+2] stored at bit index (p + OFF). Row t computed from row t-1:
   new[p] = old[p-1] ^ (old[p] | old[p+1]).
   For each row t>=1: G(t) = number of white cells at p = t-1, t-2, ... before the first black
   (cells at p < -t are white; counting stops at first black; must find one since D_1(t)=1).
   Prints G at t = 2^E, and checks G(t) == G(2^{nu2(t)}) for all t (internal consistency, no table).
   Also for t = 2^k - 1 (k>=0): B(t) = number of consecutive black cells from p = t leftwards, and
   the color right after them. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;
static int getb(const u64*a, long i){ return (a[i>>6]>>(i&63))&1; }
int main(int argc,char**argv){
  long T=atol(argv[1]);
  long OFF=T+64; long NB=2*T+192; long NW=NB/64+2;
  u64*a=calloc(NW,8),*b=calloc(NW,8);
  a[OFF>>6] |= (u64)1<<(OFF&63);
  int Gpow[64]; for(int i=0;i<64;i++) Gpow[i]=-1;
  long mism=0;
  /* row 0 handling for (c): t = 2^0 - 1 = 0 */
  for(long t=0;t<=T;t++){
    if(t>0){
      /* compute b = row t from a = row t-1, wordwise: new = (a<<1) ^ (a | (a>>1)) in bit-index terms:
         bit i of new = a[i-1] ^ (a[i] | a[i+1]). left shift moves bit i-1 to i. */
      for(long w=0; w<NW; w++){
        u64 x=a[w];
        u64 xm1 = (x<<1) | (w>0 ? a[w-1]>>63 : 0);      /* bit i holds a[i-1] */
        u64 xp1 = (x>>1) | (w+1<NW ? a[w+1]<<63 : 0);   /* bit i holds a[i+1] */
        b[w] = xm1 ^ (x | xp1);
      }
      u64*tmp=a;a=b;b=tmp;
      /* zero gap left of right edge */
      long g=0; long i=OFF+t-1;
      if(!getb(a,OFF+t)) { printf("right edge not black at t=%ld\n",t); return 1; }
      while(!getb(a,i)){ g++; i--; if(i<0){printf("ran off\n");return 1;} }
      int nu=__builtin_ctzl(t);
      if((t&(t-1))==0){ Gpow[nu]=(int)g; printf("t=2^%d G=%ld\n",nu,g); }
      else if(Gpow[nu]!=g){ mism++; if(mism<10) printf("MISMATCH t=%ld nu=%d G=%ld Gpow=%d\n",t,nu,g,Gpow[nu]); }
    }
    if(((t+1)&t)==0){ /* t = 2^k - 1 */
      long i=OFF+t, B=0; while(getb(a,i)){B++; i--;}
      int k=__builtin_ctzl(t+1);
      printf("row 2^%d-1: black run from edge B=%ld (next cell white), J+1 expected\n",k,B);
    }
  }
  printf("T=%ld mismatches=%ld\n",T,mism);
  return 0;}
