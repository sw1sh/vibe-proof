// Rule 30 from a single black cell; record columns -1,0,1,2 for t = 0..N-1.
// byte t: bit0 = cell(t,0), bit1 = cell(t,-1), bit2 = cell(t,1), bit3 = cell(t,2)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
  long N = atol(argv[1]);
  long OFF = N + 128;                 // bit index of position 0
  long W = (2 * OFF) / 64 + 4;
  uint64_t *A = calloc(W, 8), *B = calloc(W, 8);
  A[OFF / 64] |= 1ULL << (OFF % 64);
  FILE *f = fopen(argv[2], "wb");
  for (long t = 0; t < N; t++) {
    #define BIT(arr, i) ((int)(((arr)[(i) / 64] >> ((i) % 64)) & 1))
    unsigned char b = BIT(A, OFF) | (BIT(A, OFF - 1) << 1) | (BIT(A, OFF + 1) << 2) | (BIT(A, OFF + 2) << 3);
    fputc(b, f);
    long lo = (OFF - t - 2) / 64 - 1, hi = (OFF + t + 2) / 64 + 1;
    if (lo < 1) lo = 1;
    if (hi > W - 2) hi = W - 2;
    for (long k = lo; k <= hi; k++) {
      uint64_t L = (A[k] << 1) | (A[k - 1] >> 63);   // bit i <- old bit i-1  (left neighbour, p-1)
      uint64_t R = (A[k] >> 1) | (A[k + 1] << 63);   // bit i <- old bit i+1  (right neighbour, p+1)
      B[k] = L ^ (A[k] | R);
    }
    uint64_t *tmp = A; A = B; B = tmp;
  }
  fclose(f);
  return 0;
}
