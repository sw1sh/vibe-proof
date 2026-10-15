// Verifier: direct brute force of D(W) for the zero-boundary left half (catalog zrow).
// bit k of the row = depth k (k >= 1); bit 0 is the wall (always white).
// zrow (t+1) k = zrow t (k+1) xor (zrow t k || zrow t (k-1)), k >= 1.
// D(W) = max over starts supported on depths 1..W of the first even t with depth 1 white.
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  int Wmax = argc > 1 ? atoi(argv[1]) : 22;
  for (int W = 1; W <= Wmax; W++) {
    int best = -1; unsigned long long cnt = 0, witness = 0;
    for (unsigned long long s = 0; s < (1ULL << W); s++) {
      u128 x = ((u128)s) << 1;  // depths 1..W
      int t = 0, dead = -1;
      for (t = 0; t < 200; t++) {
        if (t % 2 == 0 && !((x >> 1) & 1)) { dead = t; break; }
        x = ((x >> 1) ^ (x | (x << 1))) & ~((u128)1);
      }
      if (dead < 0) { printf("W=%d start %llx survives 200 steps\n", W, s); return 1; }
      if (dead > best) { best = dead; cnt = 1; witness = s; } else if (dead == best) cnt++;
    }
    printf("W=%d D=%d count=%llu witness_bits=0x%llx\n", W, best, cnt, witness);
    fflush(stdout);
  }
  return 0;
}
