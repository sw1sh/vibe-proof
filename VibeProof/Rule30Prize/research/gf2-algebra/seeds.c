/* For every finite seed with support inside [0, w) (bit 0 set), run rule 30 for N steps and test each
   column p in [-K, w+K] for eventual periodicity: least P <= PMAX such that col(t+P) = col(t) for all t in [N/2, N-P). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int main(int argc, char **argv) {
  int w = atoi(argv[1]); long N = atol(argv[2]); int K = atoi(argv[3]); int PMAX = atoi(argv[4]);
  long W = 2 * N + w + 4; long nw = (W + 63) / 64 + 2; long off = N + 2;
  u64 *row = malloc(nw * 8), *nx = malloc(nw * 8);
  int ncol = w + 2 * K + 1; unsigned char *col = malloc((size_t)ncol * N);
  long found = 0;
  for (long seed = 1; seed < (1L << w); seed += 2) {
    memset(row, 0, nw * 8); memset(nx, 0, nw * 8);
    for (int i = 0; i < w; i++) if ((seed >> i) & 1) { long b = off + i; row[b >> 6] |= 1ULL << (b & 63); }
    for (long t = 0; t < N; t++) {
      for (int c = 0; c < ncol; c++) { long b = off - K + c; col[(size_t)c * N + t] = (row[b >> 6] >> (b & 63)) & 1; }
      long lo = (off - t - 2) / 64 - 1; if (lo < 0) lo = 0;
      long hi = (off + w + t + 2) / 64 + 1; if (hi > nw - 1) hi = nw - 1;
      for (long q = lo; q <= hi; q++) {
        u64 l = (row[q] << 1) | (q > 0 ? row[q - 1] >> 63 : 0);
        u64 r = (row[q] >> 1) | (q + 1 < nw ? row[q + 1] << 63 : 0);
        nx[q] = l ^ (row[q] | r);
      }
      u64 *tmp = row; row = nx; nx = tmp;
    }
    for (int c = 0; c < ncol; c++) {
      unsigned char *s = col + (size_t)c * N;
      for (int P = 1; P <= PMAX; P++) {
        long t; for (t = N / 2; t + P < N; t++) if (s[t] != s[t + P]) break;
        if (t + P >= N) { printf("seed=%lx column %d periodic P=%d on [N/2,N)\n", seed, c - K, P); found++; break; }
      }
    }
  }
  printf("w=%d N=%ld: %ld (seed, column) pairs look eventually periodic\n", w, N, found);
  return 0;
}
