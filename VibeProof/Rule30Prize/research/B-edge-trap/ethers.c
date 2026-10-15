// rule-30 ethers: ring Z/q configurations on cycles of length r <= RMAX; print primitive column words (canonical rotation)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static inline uint32_t stepq(uint32_t x, int q) { uint32_t m = (q == 32) ? 0xffffffffu : ((1u << q) - 1);
  uint32_t left = ((x << 1) | (x >> (q - 1))) & m, right = ((x >> 1) | (x << (q - 1))) & m; return (left ^ (x | right)) & m; }
int main(int argc, char **argv) {
  int QMAX = atoi(argv[1]), RMAX = atoi(argv[2]);
  // store found words as strings in a simple table
  static char words[100000][40]; static int wq[100000], wr[100000]; int nw = 0;
  for (int q = 1; q <= QMAX; q++) {
    for (uint32_t x = 0; x < (1u << q); x++) {
      uint32_t y = x; int r = 0;
      for (int i = 1; i <= RMAX; i++) { y = stepq(y, q); if (y == x) { r = i; break; } }
      if (!r) continue;
      uint32_t rows[64]; rows[0] = x; for (int i = 1; i < r; i++) rows[i] = stepq(rows[i - 1], q);
      for (int p = 0; p < q; p++) {
        char col[40]; for (int i = 0; i < r; i++) col[i] = '0' + ((rows[i] >> p) & 1); col[r] = 0;
        int L = r; for (int d = 1; d <= r; d++) if (r % d == 0) { int ok = 1; for (int i = d; i < r; i++) if (col[i] != col[i - d]) { ok = 0; break; } if (ok) { L = d; break; } }
        char best[40]; strncpy(best, col, L); best[L] = 0;
        for (int s = 1; s < L; s++) { char rot[40]; for (int i = 0; i < L; i++) rot[i] = col[(i + s) % L]; rot[L] = 0; if (strcmp(rot, best) < 0) strcpy(best, rot); }
        int seen = 0; for (int i = 0; i < nw; i++) if (!strcmp(words[i], best)) { seen = 1; break; }
        if (!seen && nw < 100000) { strcpy(words[nw], best); wq[nw] = q; wr[nw] = r; nw++; }
      }
    }
  }
  for (int i = 0; i < nw; i++) printf("%s (first seen q=%d r=%d)\n", words[i], wq[i], wr[i]);
  return 0;
}
