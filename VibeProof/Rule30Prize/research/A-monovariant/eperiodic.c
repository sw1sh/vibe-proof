// Which eventually periodic left-infinite rows L = u v^inf (u of length a, v primitive of length q) survive the
// phase-0 constraint for T steps?  x_1(t) depends only on L(1..t+1), so simulate on a window of width T+2.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define T 240
#define N (T + 4)
static unsigned char row[N + 4], nrow[N + 4];
int survives(const unsigned char *L) {
  memcpy(row, L, N);
  for (int t = 0; t <= T; t++) {
    if (!(t & 1) && !row[1]) return t;
    // x_k' = x_{k+1} ^ (x_k | x_{k-1}), row[0] = 0 wall, valid for k <= N - 1 - t
    for (int k = 1; k < N - 1; k++) nrow[k] = row[k + 1] ^ (row[k] | row[k - 1]);
    nrow[0] = 0; nrow[N - 1] = 0;
    memcpy(row, nrow, N);
  }
  return -1;
}
int primitive(uint32_t v, int q) {
  for (int d = 1; d < q; d++) if (q % d == 0) {
    int ok = 1;
    for (int i = 0; i < q; i++) if (((v >> i) & 1) != ((v >> (i % d)) & 1)) { ok = 0; break; }
    if (ok) return 0;
  }
  return 1;
}
int main(int argc, char **argv) {
  int amax = atoi(argv[1]), qmax = atoi(argv[2]);
  unsigned char L[N + 4];
  for (int q = 1; q <= qmax; q++) {
    for (uint32_t v = 0; v < (1u << q); v++) {
      if (!primitive(v, q)) continue;
      long found = 0; int besta = -1; uint32_t bestu = 0;
      for (int a = 0; a <= amax; a++) {
        for (uint32_t u = 0; u < (1u << a); u++) {
          // canonical: the period should start right after u; require u's last bit != v's last bit (else shorter preperiod)
          if (a > 0 && (((u >> (a - 1)) & 1) == ((v >> (q - 1)) & 1))) continue;
          L[0] = 0;
          for (int k = 1; k < N; k++) {
            int i = k - 1;
            L[k] = (i < a) ? ((u >> i) & 1) : ((v >> ((i - a) % q)) & 1);
          }
          if (survives(L) < 0) { found++; if (besta < 0) { besta = a; bestu = u; } }
        }
      }
      if (found) {
        printf("q=%d v=", q);
        for (int i = 0; i < q; i++) putchar((v >> i) & 1 ? '1' : '0');
        printf(" : %ld survivors with preperiod <= %d; e.g. u=", found, amax);
        for (int i = 0; i < besta; i++) putchar((bestu >> i) & 1 ? '1' : '0');
        printf("\n");
      }
    }
  }
}
