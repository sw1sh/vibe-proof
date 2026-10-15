// GP1 check: rule 30 from random finite seeds; are any columns near the seed eventually periodic?
// Test: column p over times [S/2, S) equal to its shift by P for some P <= PMAX.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define S 4000
#define WORDS ((2*S + 128) / 64 + 2)
#define NC 81
#define PMAX 400
static uint64_t a[WORDS], b[WORDS];
static unsigned char col[NC][S];
static uint64_t rng = 88172645463325252ULL ^ 0x9E3779B97F4A7C15ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
int main(int argc, char **argv) {
  int seeds = atoi(argv[1]); long found = 0;
  for (int sd = 0; sd < seeds; sd++) {
    memset(a, 0, sizeof a);
    int w = 1 + xr() % 24; uint64_t bits = xr() & ((1ULL << w) - 1); bits |= 1ULL | (1ULL << (w - 1));
    long off = S + 64;                       // position 0 <-> bit off
    for (int i = 0; i < w; i++) if (bits >> i & 1) { long q = off + i; a[q >> 6] |= 1ULL << (q & 63); }
    for (int t = 0; t < S; t++) {
      for (int c = 0; c < NC; c++) { long q = off + w / 2 + (c - NC / 2); col[c][t] = (a[q >> 6] >> (q & 63)) & 1; }
      // b = (a << 1) ^ (a | (a >> 1)) in position terms: new(p) = old(p-1) ^ (old(p) | old(p+1))
      // bit index increases with position: old(p-1) is bit-1 -> shift left by 1; old(p+1) -> shift right by 1
      for (int k = 0; k < WORDS; k++) {
        uint64_t l = (a[k] << 1) | (k ? a[k-1] >> 63 : 0);
        uint64_t r = (a[k] >> 1) | (k + 1 < WORDS ? a[k+1] << 63 : 0);
        b[k] = l ^ (a[k] | r);
      }
      memcpy(a, b, sizeof a);
    }
    for (int c = 0; c < NC; c++) {
      for (int P = 1; P <= PMAX; P++) {
        int ok = 1;
        for (int t = S / 2; t + P < S; t++) if (col[c][t] != col[c][t + P]) { ok = 0; break; }
        if (ok) { found++; printf("seed %d (w=%d bits=%llx) column offset %d looks periodic with P=%d\n", sd, w, (unsigned long long)bits, c - NC/2, P); break; }
      }
    }
  }
  printf("seeds=%d columns tested=%d eventually-periodic-looking columns=%ld\n", seeds, seeds * NC, found);
  return 0;
}
