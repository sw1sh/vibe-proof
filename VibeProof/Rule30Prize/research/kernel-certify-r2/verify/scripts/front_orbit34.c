// Verifier: own implementation of the front-window orbit (K = 32) for the 16 classes (m mod 2, v),
// derived from the ZBL rule: window bit i = depth f+i, stripe below the front f.
//   new_i = W_i xor (W_{i-1} | W_{i-2}),  W_{-1} = stripe(f-1), W_{-2} = stripe(f-2)
// Arrival at f = 1 (time d-1): simulate the ZBL on depths 1..K (wall white) for s = 0..31 and record the
// first s with (d-1+s) even and depth 1 white. Reports cycle length and max survival per class.
#include <stdio.h>
#include <stdint.h>
#define K 34
static int stripe(int k) { return k & 1; }
int main(void) {
  int overall = -1;
  for (int q = 0; q < 2; q++) for (int v = 0; v < 8; v++) {
    int bits[3] = { v & 1, (v >> 1) & 1, (v >> 2) & 1 };
    // first deviation offset delta: depth m+j (j >= 1) has bit vget(j-1) vs stripe(q+j)
    int delta = -1;
    for (int j = 1; j <= 5; j++) { int vb = j - 1 < 3 ? bits[j - 1] : 0; if (vb != stripe(q + j)) { delta = j; break; } }
    uint64_t W0 = 0;
    for (int i = 0; i < K; i++) { int idx = delta - 1 + i; int vb = idx < 3 ? bits[idx] : 0; if (vb) W0 |= 1ULL << i; }
    int p0 = (q + delta) & 1;  // parity of the front depth d at time 0
    uint64_t W = W0; int fp = p0; long lam = -1; int maxs = -1; long argj = -1;
    const uint64_t MASK = (K == 64) ? ~0ULL : ((1ULL << K) - 1);
    for (long j = 0; j < (1L << 22); j++) {
      if (j > 0 && W == W0 && fp == p0) { lam = j; break; }
      // arrival index j means d - 1 = j (mod lam); needs front parity 1 at the arrival, i.e. fp == 1 here
      if (fp == 1) {
        // window = depths 1..K at time d-1; d-1 has parity of j? d = j + 1 (mod lam, lam even) -> (d-1) % 2 = j % 2
        uint64_t x = W << 1;  // bit k = depth k, bit 0 wall
        int s;
        for (s = 0; s < K; s++) {
          if (((j + s) & 1) == 0 && !((x >> 1) & 1)) break;
          x = ((x >> 1) ^ (x | (x << 1))) & ~1ULL;
        }
        if (s >= K) { printf("q=%d v=%d j=%ld: no death within %d\n", q, v, j, K); }
        if (s > maxs) { maxs = s; argj = j; }
      }
      // front step: f -> f-1
      int wm1 = (fp == 0) ? 1 : 0;  // stripe(f-1): f even -> f-1 odd -> black
      int wm2 = (fp == 0) ? 0 : 1;  // stripe(f-2)
      uint64_t sh1 = (W << 1) | (uint64_t)wm1;
      uint64_t sh2 = (W << 2) | ((uint64_t)wm1 << 1) | (uint64_t)wm2;
      W = (W ^ (sh1 | sh2)) & MASK;
      fp ^= 1;
    }
    printf("q=%d v=(%d,%d,%d) delta=%d W0=%llu p0=%d cycle=%ld max_survival=%d (index %ld)\n",
           q, bits[0], bits[1], bits[2], delta, (unsigned long long)W0, p0, lam, maxs, argj);
    if (maxs > overall) overall = maxs;
  }
  printf("overall max post-arrival survival = %d\n", overall);
  return 0;
}
