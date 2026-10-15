/* Count distinct length-t traces of columns (0,1) of rule 30 over all initial conditions.
   cells (t',0),(t',1) for t'<t depend on x[-t+1 .. t] (2t cells). Encode trace as 2t bits; use a bitmap. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(){
  for(int t=1;t<=12;t++){
    int n=2*t; /* cells x[-t+1..t] -> indices 0..n-1, column 0 is index t-1, column 1 index t */
    unsigned long long N=1ULL<<n;
    unsigned char *seen=calloc((size_t)(N/8+1),1);
    unsigned long long cnt=0;
    unsigned char a[64],b[64];
    for(unsigned long long x=0;x<N;x++){
      int len=n; for(int i=0;i<n;i++) a[i]=(x>>i)&1;
      unsigned long long code=0; int off=0; /* index of global position p is p+(t-1)-off after trimming */
      for(int s=0;s<t;s++){
        int i0=(t-1)-off; /* column 0 index in current array */
        code|=((unsigned long long)a[i0])<<(2*s); code|=((unsigned long long)a[i0+1])<<(2*s+1);
        if(s==t-1) break;
        /* evolve: new array has len-2 cells, new[i]=f(a[i],a[i+1],a[i+2]) at position shifted by 1 */
        for(int i=0;i+2<len;i++) b[i]=a[i]^(a[i+1]|a[i+2]);
        len-=2; off+=1; memcpy(a,b,len);
      }
      if(!(seen[code>>3]&(1<<(code&7)))){seen[code>>3]|=1<<(code&7);cnt++;}
    }
    printf("t=%d pairs=%llu  ratio_to_prev=%s\n",t,cnt,"");
    fflush(stdout);
    free(seen);
  }
  return 0;
}
