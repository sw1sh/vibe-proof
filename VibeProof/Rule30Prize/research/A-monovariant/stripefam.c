// D(stripe^n + tail) for tails of length r, n = 0..N
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static inline u128 step(u128 r) { return (r >> 1) ^ (r | (r << 1)); }
int death(u128 L, int maxT) {
  u128 r = L; int t = 0;
  while (1) { if ((t & 1) == 0 && !(r & 1)) return t; if (t >= maxT) return -1; r = step(r); t++; }
}
int main(int argc, char **argv) {
  int rmax = atoi(argv[1]); int N = atoi(argv[2]);
  // stripe bits: x_k = 1 for k odd -> bit (k-1) = 1 for k odd -> bits 0,2,4,...
  for (int r = 1; r <= rmax; r++) {
    int bestexcess = -1000; uint64_t besttail = 0; int bestn = 0;
    for (uint64_t tail = 1ull << (r-1); tail < (1ull << r); tail++) {
      for (int n = 0; n <= N; n++) {
        u128 L = 0;
        for (int k = 1; k <= n; k++) if (k & 1) L |= (u128)1 << (k-1);
        L |= ((u128)tail) << n;
        int D = death(L, 100 + 3*(n + r));
        if (D < 0) { printf("SURVIVES r=%d tail=%llx n=%d\n", r, (unsigned long long)tail, n); continue; }
        int ex = D - n;
        if (ex > bestexcess) { bestexcess = ex; besttail = tail; bestn = n; }
      }
    }
    printf("r=%2d: max over tails, n<=%d of D - n = %d (tail=", r, N, bestexcess);
    for (int i = 0; i < r; i++) putchar((besttail >> i) & 1 ? '1' : '0');
    printf(", n=%d)\n", bestn);
    fflush(stdout);
  }
}
