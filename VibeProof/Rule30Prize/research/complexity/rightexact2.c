// Exact set of column-1 output words realizable by SOME right half under driver w^inf (phase 0 at T).
// Outputs: column 1 at every phase in 'ph' (string of digits), for n periods. Light cone brute force.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
  const char *w = argv[1]; int n = atoi(argv[2]); const char *ph = argv[3];
  int P = strlen(w); int cw[64]; for (int i = 0; i < P; i++) cw[i] = w[i] - '0';
  int isout[64] = {0}; int nout = 0; for (int i = 0; ph[i]; i++) { isout[ph[i]-'0'] = 1; nout++; }
  int steps = n * P; int width = steps; int bits = n * nout;
  if (width > 34 || bits > 30) { fprintf(stderr, "too big\n"); return 1; }
  uint64_t nz = 1ULL << bits; uint8_t *seen = calloc(nz, 1);
  for (uint64_t R = 0; R < (1ULL << width); R++) {
    uint64_t row = R, z = 0; int k = 0;
    for (int t = 0; t < steps; t++) {
      if (isout[t % P]) { z |= (row & 1) << k; k++; }
      uint64_t left = (row << 1) | (uint64_t)cw[t % P];
      row = left ^ (row | (row >> 1));
    }
    seen[z] = 1;
  }
  long cnt = 0; for (uint64_t z = 0; z < nz; z++) cnt += seen[z];
  printf("w=%s n=%d periods, outputs at phases %s: realizable %ld of 2^%d\n", w, n, ph, cnt, bits);
  return 0;
}
