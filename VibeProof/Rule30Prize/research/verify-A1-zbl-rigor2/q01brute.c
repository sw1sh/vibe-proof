/* Brute force: every row L with support exactly [1..W] (L1 = 1 required since zrow L 0 1 = L 1),
   ZBL evolution new[k] = old[k+1] ^ (old[k] | old[k-1]) for k >= 1, cell 0 white.
   Report the latest even time 2s at which column 1 first turns white, and survivors to horizon. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define NW 7
typedef struct { uint64_t w[NW]; } row;
static inline int bit1(const row *r) { return (r->w[0] >> 1) & 1; }
static inline void step(const row *a, row *o) {
  for (int i = 0; i < NW; i++) {
    uint64_t r = (a->w[i] >> 1) | (i + 1 < NW ? (a->w[i + 1] << 63) : 0);
    uint64_t l = (a->w[i] << 1) | (i > 0 ? (a->w[i - 1] >> 63) : 0);
    o->w[i] = r ^ (a->w[i] | l);
  }
  o->w[0] &= ~1ULL;
}
int main(int argc, char **argv) {
  int Wmax = atoi(argv[1]);
  for (int W = 1; W <= Wmax; W++) {
    int H = 6 * W + 64; /* horizon in time steps */
    if (W + H + 2 > 64 * NW) { printf("overflow\n"); return 1; }
    uint64_t n = (W >= 2) ? (1ULL << (W - 2)) : 1;
    long maxdeath = -1, survivors = 0; uint64_t argmax = 0;
    for (uint64_t m = 0; m < n; m++) {
      row a = {{0}};
      /* bit 1 and bit W set, bits 2..W-1 from m */
      a.w[0] |= 2ULL;
      for (int k = 2; k <= W - 1; k++) if ((m >> (k - 2)) & 1) a.w[k >> 6] |= 1ULL << (k & 63);
      if (W >= 1) a.w[W >> 6] |= 1ULL << (W & 63);
      int t = 0, dead = -1;
      while (t < H) {
        row b, c2; step(&a, &b); step(&b, &c2); a = c2; t += 2;
        if (!bit1(&a)) { dead = t; break; }
      }
      if (dead < 0) survivors++;
      else if (dead > maxdeath) { maxdeath = dead; argmax = m; }
    }
    printf("W=%2d rows=%10llu  latest first-violation time=%4ld (=%.2f W)  survivors to t=%d: %ld\n",
           W, (unsigned long long)n, maxdeath, (double)maxdeath / W, H, survivors);
    fflush(stdout);
  }
  return 0;
}
