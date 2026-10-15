/* Like absorbscan2 but only for one period P, and only counts words absorbed in all K trials. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
  int P = atoi(argv[1]); long N = atol(argv[2]); int K = atoi(argv[3]); int verbose = argc > 4;
  long L0max = 300; long W = N + L0max + 70; long nw = W / 64 + 2;
  u64 *row = malloc(nw * 8), *nx = malloc(nw * 8);
  unsigned char *col = malloc(N);
  long nprim = 0, nabs = 0;
  for (long wd = 0; wd < (1L << P); wd++) {
    int prim = 1, minrot = 1;
    for (int d = 1; d < P && prim; d++) if (P % d == 0) { int same = 1; for (int i = 0; i < P; i++) if (((wd >> i) & 1) != ((wd >> (i % d)) & 1)) same = 0; if (same) prim = 0; }
    for (int r = 1; r < P && minrot; r++) { long rot = ((wd >> r) | (wd << (P - r))) & ((1L << P) - 1); if (rot < wd) minrot = 0; }
    if (!prim || !minrot) continue;
    nprim++;
    int absorbed = 0, per = 0;
    for (int k = 0; k < K; k++) {
      memset(row, 0, nw * 8); memset(nx, 0, nw * 8);
      long L0 = 20 + rnd() % (L0max - 20);
      for (long i = 0; i < L0; i++) if (rnd() & 1) row[i >> 6] |= 1ULL << (i & 63);
      for (long t = 0; t < N; t++) {
        col[t] = row[0] & 1;
        int c = (wd >> (t % P)) & 1;
        long hi = (L0 + t + 2) / 64 + 1; if (hi > nw - 1) hi = nw - 1;
        for (long q = 0; q <= hi; q++) {
          u64 l = (row[q] << 1) | (q > 0 ? row[q - 1] >> 63 : (u64)c);
          u64 r = (row[q] >> 1) | (q + 1 < nw ? row[q + 1] << 63 : 0);
          nx[q] = l ^ (row[q] | r);
        }
        u64 *tmp = row; row = nx; nx = tmp;
      }
      int found = 0;
      for (int Pp = 1; Pp <= 1024 && !found; Pp++) { long t; for (t = N / 2; t + Pp < N; t++) if (col[t] != col[t + Pp]) break; if (t + Pp >= N) found = Pp; }
      if (found) { absorbed++; per = found; } else break;
    }
    if (absorbed == K) { nabs++; if (verbose) { printf("  w="); for (int i = 0; i < P; i++) putchar('0' + ((wd >> i) & 1)); printf(" col1 period %d\n", per); } }
  }
  printf("P=%d: %ld primitive words (up to rotation), %ld absorbed in all %d trials\n", P, nprim, nabs, K);
  return 0;
}
