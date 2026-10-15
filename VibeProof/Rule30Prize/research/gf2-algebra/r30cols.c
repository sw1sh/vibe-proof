/* Rule 30 from a single 1 at position 0. Prints columns -K..K for t = 0..N-1,
   one line per column: "p bits". Bitset rows over positions [-N, N]. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int main(int argc, char **argv) {
  long N = atol(argv[1]); int K = atoi(argv[2]);
  long W = 2 * N + 3; long nw = (W + 63) / 64 + 2;
  u64 *row = calloc(nw, 8), *nx = calloc(nw, 8);
  long off = N + 1; /* bit index of position 0 */
  row[off >> 6] |= 1ULL << (off & 63);
  char **col = malloc((2 * K + 1) * sizeof(char *));
  for (int k = 0; k <= 2 * K; k++) col[k] = malloc(N + 1);
  for (long t = 0; t < N; t++) {
    for (int k = -K; k <= K; k++) { long b = off + k; col[k + K][t] = '0' + ((row[b >> 6] >> (b & 63)) & 1); }
    /* new(p) = old(p-1) ^ (old(p) | old(p+1)); bit i <-> position i - off.
       old(p-1) at bit i-1 -> shift left by 1; old(p+1) at bit i+1 -> shift right by 1 */
    long lo = (off - t - 2) / 64 - 1; if (lo < 0) lo = 0;
    long hi = (off + t + 2) / 64 + 1; if (hi > nw - 1) hi = nw - 1;
    for (long w = lo; w <= hi; w++) {
      u64 l = (row[w] << 1) | (w > 0 ? row[w - 1] >> 63 : 0);
      u64 r = (row[w] >> 1) | (w + 1 < nw ? row[w + 1] << 63 : 0);
      nx[w] = l ^ (row[w] | r);
    }
    u64 *tmp = row; row = nx; nx = tmp;
  }
  for (int k = -K; k <= K; k++) { col[k + K][N] = 0; printf("%d %s\n", k, col[k + K]); }
  return 0;
}
