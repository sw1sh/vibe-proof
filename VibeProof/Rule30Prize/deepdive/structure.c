/* structure.c — tests a 0/1 sequence (ASCII '0'/'1', s(0), s(1), ...) for structure.
 *
 *   1. 2-kernel growth: number of distinct subsequences n -> s(2^k n + r), r < 2^k, truncated
 *      to length L. Bounded in k for 2-automatic sequences; equal to 2^k for random ones.
 *   2. Linear complexity over GF(2) (Berlekamp-Massey) of prefixes; about n/2 when random.
 *   3. Zero-run length histogram against the geometric law of a random sequence.
 *
 * usage: structure file [N_for_BM]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int cmpu(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("open"); return 2; }
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  unsigned char *s = malloc(n);
  if (fread(s, 1, n, f) != (size_t)n) return 2;
  fclose(f);
  for (long i = 0; i < n; i++) s[i] &= 1;  /* accepts raw 0/1 bytes or ASCII '0'/'1' */
  printf("length %ld\n", n);

  /* 1. 2-kernel with L = 40 */
  const int L = 40;
  printf("2-kernel (L=%d): k  distinct  of 2^k\n", L);
  for (int k = 0; (1L << k) * L <= n && k <= 16; k++) {
    long m = 1L << k;
    uint64_t *v = malloc(m * sizeof(uint64_t));
    for (long r = 0; r < m; r++) {
      uint64_t w = 0;
      for (int j = 0; j < L; j++) w = (w << 1) | s[m * j + r];
      v[r] = w;
    }
    qsort(v, m, sizeof(uint64_t), cmpu);
    long d = m ? 1 : 0;
    for (long r = 1; r < m; r++) d += v[r] != v[r - 1];
    printf("   %2d  %6ld  %6ld\n", k, d, m);
    free(v);
  }

  /* 2. Berlekamp-Massey over GF(2), bit-packed */
  long N = argc > 2 ? atol(argv[2]) : 16384;
  if (N > n) N = n;
  long W = N / 64 + 2;
  uint64_t *C = calloc(W, 8), *B = calloc(W, 8), *T = calloc(W, 8);
  C[0] = B[0] = 1;                       /* connection polynomials, bit i = coeff of x^i */
  long Lc = 0, mshift = 1;
  printf("linear complexity: n  L(n)  n/2\n");
  long next = 1024;
  for (long i = 0; i < N; i++) {
    int d = s[i];                         /* discrepancy */
    for (long j = 1; j <= Lc; j++) d ^= ((C[j >> 6] >> (j & 63)) & 1) & s[i - j];
    if (d) {
      memcpy(T, C, W * 8);
      /* C ^= B << mshift */
      long ws = mshift >> 6; int bs = mshift & 63;
      for (long j = W - 1; j >= ws; j--) {
        uint64_t val = B[j - ws] << bs;
        if (bs && j - ws - 1 >= 0) val |= B[j - ws - 1] >> (64 - bs);
        C[j] ^= val;
      }
      if (2 * Lc <= i) { Lc = i + 1 - Lc; memcpy(B, T, W * 8); mshift = 1; } else mshift++;
    } else mshift++;
    if (i + 1 == next) { printf("   %7ld  %7ld  %7ld\n", i + 1, Lc, (i + 1) / 2); next *= 2; }
  }

  /* 3. zero-run histogram (runs bounded by 1s on both sides) */
  long hist[64] = {0}, runs = 0, run = 0, started = 0;
  for (long i = 0; i < n; i++) {
    if (s[i]) { if (started) { hist[run < 63 ? run : 63]++; runs++; } started = 1; run = 0; }
    else run++;
  }
  printf("zero runs between 1s: length  count  expected(geometric)\n");
  for (int j = 0; j <= 24; j++)
    printf("   %2d  %8ld  %10.1f\n", j, hist[j], runs / (double)(2L << j));
  return 0;
}
