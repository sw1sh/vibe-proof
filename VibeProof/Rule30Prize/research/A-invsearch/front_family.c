// Family x0 = S[1..m] . 1 (m odd): stripe up to depth m, extra black cell at depth m+1, zeros beyond.
// Front-frame orbit: window W_t (64 bits) at depths f_t .. f_t+63, f_t = m+1-t; W_0 = 1 (only the front cell).
// The orbit does not depend on m (stripe ahead; parity of f_t = parity of (m+1-t) = parity of t since m+1 even).
// At t = m (odd) the front reaches depth 1: post-arrival survival sigma(m) from the 64-bit window.
// Also cross-check against direct simulation for small m.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int S(long k){ return (int)(k & 1); }
int main(int argc, char **argv){
  long Tmax = atol(argv[1]);
  uint64_t W = 1;               // depth f: front cell (black where stripe is white)
  int hist[128] = {0}; int best = -1; long bestm = -1;
  long fpar_base = 0;           // f_t = m+1-t; only parity matters: (m+1-t) even when t even
  for (long t = 0; t <= Tmax; t++){
    if (t & 1){
      // arrival for m = t (odd): f = 1; config bits i <-> depth i+1
      uint64_t x = W;
      int s;
      for (s = 0; s < 62; s++){
        long time = t + s;
        if (!(time & 1) && !(x & 1)) break;
        x = (x >> 1) ^ (x | (x << 1));
      }
      if (s >= 62) { printf("m=%ld: survival beyond reliable horizon\n", t); fflush(stdout); }
      hist[s]++;
      if (s > best){ best = s; bestm = t; printf("new max sigma=%d at m=%ld (binary ", s, t);
        for (int b = 30; b >= 0; b--) putchar(((t >> b) & 1) ? '1' : '0'); printf(")\n"); fflush(stdout); }
    }
    // front step: f = f_t; parity of f_t: (m+1-t) mod 2 with m odd => (t mod 2 == 0) ? even : odd
    int fe = (t & 1) ? 1 : 0;   // f odd iff t odd
    // S(f-1), S(f-2): f-1 has parity 1-fe... S(k) = k mod 2
    int s1 = (fe ^ 1), s2 = fe;   // S(f-1) = (f-1) mod 2, S(f-2) = f mod 2
    W = W ^ (((W << 1) | (uint64_t)s1) | ((W << 2) | ((uint64_t)s1 << 1) | (uint64_t)s2));
  }
  printf("histogram of sigma: "); for (int i = 0; i < 64; i++) if (hist[i]) printf("%d:%d ", i, hist[i]); printf("\n");
  return 0;
}
