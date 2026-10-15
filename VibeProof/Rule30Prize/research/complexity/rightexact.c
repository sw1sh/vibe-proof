// Exact set of words z_k = col1(T+2k+1), k < n, realizable by SOME right half when column 0 follows
// the periodic word w (phase 0 at time T). Brute force over right halves restricted to the light cone
// [1, 2n] (cells further right cannot reach column 1 within 2n steps). outph: phase(s) within w at which
// column 1 is recorded.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
  const char *w = argv[1]; int n = atoi(argv[2]); int outph = atoi(argv[3]);
  int P = strlen(w); int cw[64]; for (int i = 0; i < P; i++) cw[i] = w[i] - '0';
  int steps = n * P;               // record n outputs (one per period)
  int width = steps;               // cells 1..width (bit i <-> cell i+1)
  if (width > 40) { fprintf(stderr, "too wide\n"); return 1; }
  uint64_t nz = 1ULL << n; uint8_t *seen = calloc(nz, 1);
  uint64_t total = 1ULL << width;
  for (uint64_t R = 0; R < total; R++) {
    uint64_t row = R, z = 0; int k = 0;
    for (int t = 0; t < steps; t++) {
      if (t % P == outph) { z |= (row & 1) << k; k++; }
      int c = cw[t % P];
      uint64_t left = (row << 1) | (uint64_t)c;   // cell i-1 (cell 0 = c)
      uint64_t right = row >> 1;                   // cell i+1 (beyond width: 0, irrelevant within cone)
      row = left ^ (row | right);
    }
    seen[z] = 1;
  }
  long cnt = 0; for (uint64_t z = 0; z < nz; z++) cnt += seen[z];
  printf("w=%s n=%d outph=%d: realizable %ld of %llu\n", w, n, outph, cnt, (unsigned long long)nz);
  if (argc > 4) { for (uint64_t z = 0; z < nz; z++) if (seen[z]) { for (int i = 0; i < n; i++) putchar('0' + ((z >> i) & 1)); putchar('\n'); } }
  return 0;
}
