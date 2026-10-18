#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
// max and average number of column-1 words per column-0 word, L = 1..14 (n = L + 1 times)
int main(void) {
  for (int L = 10; L <= 14; L++) {
    int W = 2 * L + 2;
    uint64_t nconf = 1ULL << W, mask = (1ULL << W) - 1;
    uint64_t nw = 1ULL << (2 * (L + 1));
    uint8_t *seen = calloc(nw / 8 + 1, 1);
    uint32_t *mult = calloc(1ULL << (L + 1), sizeof(uint32_t));
    if (!seen || !mult) { printf("oom\n"); return 1; }
    for (uint64_t x = 0; x < nconf; x++) {
      uint64_t y = x, u = 0, v = 0;
      for (int t = 0; t <= L; t++) {
        u |= ((y >> L) & 1) << t; v |= ((y >> (L + 1)) & 1) << t;
        y = ((y << 1) ^ (y | (y >> 1))) & mask;
      }
      uint64_t w = u | (v << (L + 1));
      if (!(seen[w >> 3] & (1 << (w & 7)))) { seen[w >> 3] |= 1 << (w & 7); mult[u]++; }
    }
    uint32_t mx = 0; double avg = 0;
    for (uint64_t u = 0; u < (1ULL << (L + 1)); u++) { if (mult[u] > mx) mx = mult[u]; avg += mult[u]; }
    avg /= (double)(1ULL << (L + 1));
    printf("L=%2d max=%u avg=%.3f\n", L, mx, avg);
    fflush(stdout);
    free(seen); free(mult);
  }
  return 0;
}
