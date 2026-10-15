// Factor complexity of the white-time column-1 output y of a right half driven by an alternating center.
// Usage: rightcomplex T0 N phase mode   (mode 0: true rule-30 right half at time T0; mode 1: random finite support T0)
// Output: kick density vs the 10000 wheel, and p(n) = #distinct factors of length n in y, n = 4..64.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int cmp(const void*a,const void*b){u64 x=*(u64*)a,y=*(u64*)b;return x<y?-1:x>y;}
int main(int argc,char**argv){
  long T0=atol(argv[1]),N=atol(argv[2]); int ph=atoi(argv[3]),mode=atoi(argv[4]);
  long W=T0+N+130; long nw=W/64+2;
  u64 *a=calloc(nw,8),*b=calloc(nw,8);
  // bit p of a = cell at column p (p>=0); column 0 is the driver
  if(mode==0){ // full single-seed rule 30 to time T0, keep columns >= 0
    long FW=2*T0+130, fnw=FW/64+2, off=T0+64; u64*f=calloc(fnw,8),*g=calloc(fnw,8);
    f[off/64]|=1ULL<<(off%64);
    for(long t=0;t<T0;t++){ // new[p] = old[p-1] ^ (old[p] | old[p+1])
      for(long i=0;i<fnw;i++){u64 x=f[i];u64 l=(x<<1)|(i?f[i-1]>>63:0);u64 r=(x>>1)|(i+1<fnw?f[i+1]<<63:0);g[i]=l^(x|r);}
      u64*tmp=f;f=g;g=tmp;}
    for(long p=1;p<=T0+1 && p<W;p++){long q=off+p; if((f[q/64]>>(q%64))&1) a[p/64]|=1ULL<<(p%64);}
  } else { srand(12345+T0); for(long p=1;p<=T0;p++) if(rand()&1) a[p/64]|=1ULL<<(p%64); }
  fprintf(stderr,"init done\n"); long ny=0; unsigned char*y=malloc(N/2+10);
  long kick=0, wh=0;
  for(long t=0;t<N;t++){
    int c=((t+ph)&1); // center at time t (alternating)
    if(c) a[0]|=1ULL; else a[0]&=~1ULL;
    if(!c){ y[ny++]=(a[0]>>1)&1; }
    long lim=(N-t)/64+3; if(lim>nw) lim=nw; // light cone: columns <= N-t+2 suffice
    for(long i=0;i<lim;i++){u64 x=a[i];u64 l=(x<<1)|(i?a[i-1]>>63:0);u64 r=(x>>1)|(i+1<nw?a[i+1]<<63:0);b[i]=l^(x|r);}
    for(long i=lim;i<nw;i++) b[i]=0;
    u64*tmp=a;a=b;b=tmp;
  }
  fprintf(stderr,"sim done ny=%ld\n",ny);
  // kick density relative to best-phase 10000 wheel in windows of 1000 (skip first 2000 samples)
  long st=2000, mism=0, tot=0;
  for(long w0=st; w0+1000<=ny; w0+=1000){ long best=1000; for(int s=0;s<5;s++){long m=0; for(long k=w0;k<w0+1000;k++){int e=((k+s)%5==0); m+= (y[k]!=e);} if(m<best)best=m;} mism+=best; tot+=1000; }
  printf("T0=%ld N=%ld phase=%d mode=%d samples=%ld; ones density %.4f; mismatch vs best 10000-wheel per window: %.4f\n",T0,N,ph,mode,ny-st,
    ({double s=0; for(long k=st;k<ny;k++) s+=y[k]; s/(ny-st);}), (double)mism/tot);
  { FILE*fo=fopen("y_out.txt","w"); for(long k=0;k<ny;k++) fputc('0'+y[k],fo); fclose(fo); }
  fprintf(stderr,"kick done\n"); u64*buf=malloc(8*ny);
  int ns[]={8,16,32,64,96,128,192,256,384,512,768,1024};
  for(int q=0;q<12;q++){ int n=ns[q]; if(n>ny-st) break; long m=0;
    // 64-bit polynomial rolling hash over the window (collisions negligible at these counts)
    const u64 B=0x9E3779B97F4A7C15ULL; u64 pw=1; for(int j=0;j<n;j++) pw*=B;
    u64 h=0; for(long k=st;k<st+n;k++) h=h*B+y[k]+1;
    buf[m++]=h;
    for(long k=st+n;k<ny;k++){ h=h*B+y[k]+1 - pw*(y[k-n]+1); buf[m++]=h; }
    qsort(buf,m,8,cmp); long d=m?1:0; for(long k=1;k<m;k++) if(buf[k]!=buf[k-1]) d++;
    printf("p(%d)=%ld ",n,d); fflush(stdout);}
  printf("\n"); return 0; }
