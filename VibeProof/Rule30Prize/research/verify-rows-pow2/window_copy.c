/* Right-edge window dynamics of rule 30: bit i of y = R_i(t), i = 0..127.
   F(y)_i = y_i xor (y_{i-1} or y_{i-2}),  y_0 = 1 always.
   Iterate from y = 1 (row 0), print the zero gap G(t) at t = 2^E (number of zero bits 1..G above bit 0).
   Usage: window LOGMAX [start_state_hex_hi start_state_hex_lo start_t] ; resumable. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int gap(u128 y){ int g=0; for(int i=1;i<128;i++){ if((y>>i)&1) break; g++; } return g; }
int main(int argc,char**argv){
  int LOG=atoi(argv[1]);
  u128 y=1; uint64_t t=0;
  if(argc>=5){ y=((u128)strtoull(argv[2],0,16)<<64)|strtoull(argv[3],0,16); t=strtoull(argv[4],0,10); }
  uint64_t end=(uint64_t)1<<LOG; if(argc>=6) end=strtoull(argv[5],0,10);
  uint64_t nextpow=1; while(nextpow<=t) nextpow<<=1;
  if(t==0){ printf("t=2^0 G=%d\n",gap(y)); }
  while(t<end){
    uint64_t stop = nextpow<end?nextpow:end;
    for(;t<stop;t++){ y ^= ((y<<1)|(y<<2)); }
    if(t==nextpow){ printf("t=2^%d G=%d\n",__builtin_ctzll(t),gap(y)); fflush(stdout); nextpow<<=1; }
  }
  printf("state %016llx %016llx t=%llu\n",(unsigned long long)(y>>64),(unsigned long long)y,(unsigned long long)t);
  return 0;}
