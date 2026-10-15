// Search finite rule-30 configurations with support in [-w,w] for a center column that is periodic
// (period <= PMAX) on the window [T/2, T). Heuristic counterexample search for the finite-configuration
// generalization of Problem 1.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
  int w = argc > 1 ? atoi(argv[1]) : 6;
  int T = argc > 2 ? atoi(argv[2]) : 2048;
  int PMAX = argc > 3 ? atoi(argv[3]) : 512;
  int ncell = 2 * (w + T) + 3;          // positions -(w+T)-1 .. (w+T)+1
  int nw = (ncell + 63) / 64 + 2;
  int off = w + T + 1;                  // bit index of position 0
  uint64_t *x = calloc(nw, 8), *y = calloc(nw, 8);
  unsigned char *col = malloc(T);
  long found = 0, total = 0;
  uint64_t nconf = 1ULL << (2 * w + 1);
  for (uint64_t cfg = 1; cfg < nconf; cfg++) {
    memset(x, 0, nw * 8);
    for (int i = 0; i < 2 * w + 1; i++) if ((cfg >> i) & 1) { int b = off - w + i; x[b >> 6] |= 1ULL << (b & 63); }
    for (int t = 0; t < T; t++) {
      col[t] = (x[off >> 6] >> (off & 63)) & 1;
      // y_i = x_{i-1} ^ (x_i | x_{i+1}); bit i <-> position i-off
      for (int k = 0; k < nw; k++) {
        uint64_t left = (x[k] << 1) | (k > 0 ? x[k - 1] >> 63 : 0);      // bit i gets x_{i-1}
        uint64_t right = (x[k] >> 1) | (k + 1 < nw ? x[k + 1] << 63 : 0); // bit i gets x_{i+1}
        y[k] = left ^ (x[k] | right);
      }
      uint64_t *tmp = x; x = y; y = tmp;
    }
    total++;
    int s = T / 2;
    for (int p = 1; p <= PMAX; p++) {
      int ok = 1;
      for (int t = s; t + p < T; t++) if (col[t] != col[t + p]) { ok = 0; break; }
      if (ok) { found++; if (found <= 20) { printf("cfg=%llx period %d\n", (unsigned long long)cfg, p); } break; }
    }
  }
  printf("w=%d T=%d PMAX=%d configs=%ld periodic_on_window=%ld\n", w, T, PMAX, total, found);
  return 0;
}
