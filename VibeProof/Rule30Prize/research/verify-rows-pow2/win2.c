/* Independent right-edge window iteration. State: R_i(t) for i = 0..127 in (lo, hi):
   bit i of lo = R_i (i<64), bit (i-64) of hi = R_i (i>=64).
   Update: R_i(t+1) = R_i(t) ^ (R_{i-1}(t) | R_{i-2}(t)), with R_{-1} = R_{-2} = 0.
   Truncation above bit 127 is harmless: bit i depends only on bits i, i-1, i-2.
   Usage: win2 start_t end_t lo_hex hi_hex  (state at start_t). Prints gap at every power of 2 in
   (start_t, end_t], and final state. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
static int gap(u64 lo, u64 hi){
  int g=0;
  for(int i=1;i<128;i++){ int b = i<64 ? (lo>>i)&1 : (hi>>(i-64))&1; if(b) return g; g++; }
  return -1; }
int main(int argc,char**argv){
  u64 t=strtoull(argv[1],0,10), end=strtoull(argv[2],0,10);
  u64 lo=strtoull(argv[3],0,16), hi=strtoull(argv[4],0,16);
  while(t<end){
    u64 nextpow=1; while(nextpow<=t) nextpow<<=1;
    u64 stop = nextpow<end?nextpow:end;
    u64 n = stop - t;
    for(u64 s=0;s<n;s++){
      u64 l1 = lo<<1, l2 = lo<<2;
      u64 h1 = (hi<<1)|(lo>>63), h2 = (hi<<2)|(lo>>62);
      lo ^= (l1|l2); hi ^= (h1|h2);
    }
    t = stop;
    if(t==nextpow){ printf("t=2^%d G=%d\n",__builtin_ctzll(t),gap(lo,hi)); fflush(stdout); }
  }
  printf("STATE %llu %016llx %016llx\n",(unsigned long long)t,(unsigned long long)lo,(unsigned long long)hi);
  return 0;}
