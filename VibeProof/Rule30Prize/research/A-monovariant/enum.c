// Zero-boundary left half (ZBL), k-coordinates: x_0 = 0, x_k(t+1) = x_{k+1}(t) ^ (x_k(t) | x_{k-1}(t)).
// Row r: bit i = x_{i+1}.  Phase 0 constraint: x_1(t) = 1 for every even t.
// For every L of width <= W (bit W-1 may be 0 or 1), compute D(L) = first even t with x_1(t) = 0.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static inline u128 step(u128 r) { return (r >> 1) ^ (r | (r << 1)); }
int main(int argc, char **argv) {
  int Wmax = argc > 1 ? atoi(argv[1]) : 20;
  for (int W = 1; W <= Wmax; W++) {
    // only exact width W (top bit set)
    uint64_t lo = 1ull << (W - 1), hi = 1ull << W;
    int best = -1; long cntbest = 0; long hist[256] = {0};
    uint64_t ex = 0;
    for (uint64_t L = lo; L < hi; L++) {
      if (!(L & 1)) { hist[0]++; continue; }
      u128 r = L; int t = 0;
      while (1) {
        if ((t & 1) == 0 && !(r & 1)) break;
        r = step(r); t++;
        if (t > 200) { printf("W=%d L=%llx survives >200\n", W, (unsigned long long)L); break; }
      }
      hist[t]++;
      if (t > best) { best = t; cntbest = 1; ex = L; } else if (t == best) cntbest++;
    }
    printf("W=%2d maxD=%3d (count %ld) example L=", W, best, cntbest);
    for (int i = 0; i < W; i++) putchar((ex >> i) & 1 ? '1' : '0');
    printf("   hist(D even):");
    for (int t = 0; t <= best; t += 2) printf(" %ld", hist[t]);
    printf("\n");
    fflush(stdout);
  }
  return 0;
}
