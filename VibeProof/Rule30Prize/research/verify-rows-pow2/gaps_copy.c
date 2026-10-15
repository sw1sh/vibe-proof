/* Simulate rule 30 from a single cell; for each row t compute the zero gap at the right end:
   G(t) = number of consecutive zeros immediately left of the right edge cell (t,t).
   Check G(t) = J_{nu2(t)} with J_E from command-line table. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned char u8;
int main(int argc,char**argv){
  int T=atoi(argv[1]);
  int W=2*T+3; u8*a=calloc(W,1),*b=calloc(W,1); int off=T+1; a[off]=1;
  /* J_E table from e_j data */
  int e[]={0,1,1,2,3,3,4,5,5,6,6,6,6,6,6,7,8,8,8,8,8,8,8,8,9,10,10,11,11,12,12,12,12,12,13,13,14,15,15,16,16,17,17,18,18,18,18,18,19,20,20,21,21,21,22,23,23,23,24,24,25,25,25,26,27,27,28,28,28,29,30,30,31,31,32};
  int ne=sizeof(e)/sizeof(int); int J[40]; for(int E=0;E<40;E++){J[E]=-1;for(int j=0;j<ne;j++) if(e[j]<=E) J[E]=j;}
  long bad=0, checked=0;
  for(int t=1;t<=T;t++){
    for(int p=off-t;p<=off+t;p++){ b[p]=a[p-1]^(a[p]|a[p+1]); }
    b[off-t-1]=0; b[off+t+1]=0;
    u8*tmp=a;a=b;b=tmp;
    /* zero gap */
    int g=0; while(g<2*t && a[off+t-1-g]==0) g++;
    int nu=__builtin_ctz(t);
    if(nu<40 && J[nu]>=0 && J[nu]<ne-1){ checked++; if(g!=J[nu]){bad++; if(bad<10) printf("t=%d nu=%d G=%d J=%d\n",t,nu,g,J[nu]);}}
    if((t&(t-1))==0) printf("t=2^%d: G=%d J=%d\n",nu,g,J[nu]);
  }
  printf("checked %ld rows, mismatches %ld\n",checked,bad);
  return 0;}
