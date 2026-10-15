/* For each primitive word w (up to rotation), period P <= PMAX: drive K random finite right halves
   (random bits on positions 1..L0, zero beyond) with c = w^infinity for N steps; column 1 is "absorbed"
   if it is periodic (least period <= 4096) on [N/2, N). Print words absorbed in all K trials. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
  int PMAX = atoi(argv[1]); long N = atol(argv[2]); int K = atoi(argv[3]);
  long L0max = 400; long W = N + L0max + 70; long nw = W / 64 + 2;
  u64 *row = malloc(nw * 8), *nx = malloc(nw * 8);
  unsigned char *col = malloc(N);
  for (int P = 1; P <= PMAX; P++) {
    for (long wd = 0; wd < (1L << P); wd++) {
      int prim = 1, minrot = 1;
      for (int d = 1; d < P && prim; d++) if (P % d == 0) { int same = 1; for (int i = 0; i < P; i++) if (((wd >> i) & 1) != ((wd >> (i % d)) & 1)) same = 0; if (same) prim = 0; }
      for (int r = 1; r < P && minrot; r++) { long rot = ((wd >> r) | (wd << (P - r))) & ((1L << P) - 1); if (rot < wd) minrot = 0; }
      if (!prim || !minrot) continue;
      int absorbed = 0; int periods[64];
      for (int k = 0; k < K; k++) {
        memset(row, 0, nw * 8); memset(nx, 0, nw * 8);
        long L0 = 20 + rnd() % (L0max - 20);
        for (long i = 0; i < L0; i++) if (rnd() & 1) row[i >> 6] |= 1ULL << (i & 63);   /* bit i <-> position i+1 */
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
        for (int Pp = 1; Pp <= 1024 && !found; Pp++) { long t; for (t = N / 2; t + Pp < N; t++) if (col[t] != col[t + Pp]) break; if (t + Pp >= N) { found = Pp; } }
        periods[k] = found; if (found) absorbed++;
      }
      if (absorbed > 0) {
        printf("P=%d w=", P); for (int i = 0; i < P; i++) putchar('0' + ((wd >> i) & 1));
        printf("  absorbed %d/%d  col1 periods:", absorbed, K); for (int k = 0; k < K; k++) printf(" %d", periods[k]); printf("\n");
      }
    }
  }
  return 0;
}
