/* For e = 0..E: z_e = number of zeros immediately left of the right edge in row 2^e of rule 30
   (single seed), i.e. cell(2^e, 2^e - i) = 0 for 1 <= i <= z_e and cell(2^e, 2^e - z_e - 1) = 1. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
int main(int argc, char **argv) {
  int E = atoi(argv[1]); long N = 1L << E;
  long W = 2 * N + 3; long nw = (W + 63) / 64 + 2;
  u64 *row = calloc(nw, 8), *nx = calloc(nw, 8);
  long off = N + 1;
  row[off >> 6] |= 1ULL << (off & 63);
  int e = 0;
  for (long t = 0; t <= N; t++) {
    if (t == (1L << e)) {
      long z = 0; long b = off + t - 1;
      while (b >= 0 && !((row[b >> 6] >> (b & 63)) & 1)) { z++; b--; }
      printf("e=%d z_e=%ld\n", e, z); fflush(stdout); e++;
    }
    if (t == N) break;
    long lo = (off - t - 2) / 64 - 1; if (lo < 0) lo = 0;
    long hi = (off + t + 2) / 64 + 1; if (hi > nw - 1) hi = nw - 1;
    for (long w = lo; w <= hi; w++) {
      u64 l = (row[w] << 1) | (w > 0 ? row[w - 1] >> 63 : 0);
      u64 r = (row[w] >> 1) | (w + 1 < nw ? row[w + 1] << 63 : 0);
      nx[w] = l ^ (row[w] | r);
    }
    u64 *tmp = row; row = nx; nx = tmp;
  }
  return 0;
}
