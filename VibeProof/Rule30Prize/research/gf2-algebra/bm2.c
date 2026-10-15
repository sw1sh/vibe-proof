/* Berlekamp-Massey over GF(2) on the first N bits of the rule 30 center column (from center-1e7.bin).
   Prints the linear complexity L(n) at selected n and the max |L(n) - n/2| deviation. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int bit(const unsigned char *d, long i) { return (d[i >> 3] >> (7 - (i & 7))) & 1; }
int main(int argc, char **argv) {
  long N = atol(argv[1]);
  FILE *f = fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", "rb");
  unsigned char *d = malloc(1250000); fread(d, 1, 1250000, f); fclose(f);
  long W = N / 64 + 2;
  u64 *C = calloc(W, 8), *B = calloc(W, 8), *T = calloc(W, 8);
  /* s reversed store: we need discrepancy d_n = s_n + sum_{i=1..L} C_i s_{n-i}. Keep R = bits of s reversed in a bitset:
     store s_{n-i} at index i of a sliding register -> use array S where S[k] = s_k and compute dot via loop over words of C aligned. */
  /* simpler: maintain rev[k] = s_{N-1-k}; then s_{n-i} = rev[N-1-n+i]: dot(C[1..L], rev[N-1-n+1 .. ]) needs unaligned shifts. */
  u64 *rev = calloc(W + 2, 8);
  for (long k = 0; k < N; k++) if (bit(d, N - 1 - k)) rev[k >> 6] |= 1ULL << (k & 63);
  C[0] = 1; B[0] = 1; long L = 0, m = 1; double maxdev = 0; long maxdevn = 0;
  long report = 1;
  for (long n = 0; n < N; n++) {
    /* discrepancy: sum_{i=0..L} C_i s_{n-i} = sum_i C_i rev[N-1-n+i] */
    long base = N - 1 - n; int disc = 0;
    long words = L / 64 + 1;
    for (long w = 0; w < words; w++) {
      long b = base + 64 * w; long bw = b >> 6, bs = b & 63;
      u64 r = rev[bw] >> bs; if (bs) r |= rev[bw + 1] << (64 - bs);
      disc ^= __builtin_parityll(C[w] & r);
    }
    if (disc) {
      memcpy(T, C, W * 8);
      /* C = C + x^m B */
      long ws = m >> 6, bs = m & 63;
      long hiw = (L + m) / 64 + 2; if (hiw > W - 1) hiw = W - 1;
      for (long w = hiw; w >= ws; w--) {
        u64 v = B[w - ws] << bs; if (bs && w - ws - 1 >= 0) v |= B[w - ws - 1] >> (64 - bs);
        C[w] ^= v;
      }
      if (2 * L <= n) { L = n + 1 - L; memcpy(B, T, W * 8); m = 1; } else m++;
    } else m++;
    double dev = (double)L - (n + 1) / 2.0; if (dev < 0) dev = -dev;
    if (dev > maxdev) { maxdev = dev; maxdevn = n + 1; }
    if (n + 1 == report || n + 1 == N) { printf("n=%ld L=%ld L-n/2=%.1f\n", n + 1, L, L - (n + 1) / 2.0); report *= 2; }
  }
  printf("max |L(n)-n/2| = %.1f at n=%ld\n", maxdev, maxdevn);
  return 0;
}
