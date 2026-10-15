// Read c(0..N-1) from center-1e7.bin (8 per byte, MSB first). For n = 1..64 compute:
//   distinct windows of length n among positions 0..N-n, and first repeat position j_min(n).
// Uses sorting of 64-bit window keys (n <= 64).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int cmp(const void *a, const void *b) { uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
  const char *fn = argv[1]; long N = atol(argv[2]); int nlo = atoi(argv[3]), nhi = atoi(argv[4]);
  FILE *f = fopen(fn, "rb"); if (!f) return 1;
  unsigned char *buf = malloc(N/8 + 1); size_t got = fread(buf, 1, N/8 + 1, f); fclose(f);
  if ((long)got * 8 < N) { fprintf(stderr, "short read %zu\n", got); return 1; }
  unsigned char *c = malloc(N); for (long i = 0; i < N; i++) c[i] = (buf[i>>3] >> (7 - (i&7))) & 1;
  printf("first 32: "); for (int i = 0; i < 32; i++) printf("%d", c[i]); printf("\n");
  uint64_t *k = malloc(sizeof(uint64_t) * N);
  for (int n = nlo; n <= nhi; n++) {
    long M = N - n + 1; uint64_t w = 0, mask = (n == 64) ? ~0ULL : ((1ULL << n) - 1);
    for (long i = 0; i < N; i++) { w = ((w << 1) | c[i]) & mask; if (i >= n - 1) k[i - n + 1] = w; }
    qsort(k, M, sizeof(uint64_t), cmp);
    long distinct = 1; for (long i = 1; i < M; i++) if (k[i] != k[i-1]) distinct++;
    printf("n=%d windows=%ld distinct=%ld %s\n", n, M, distinct, distinct == M ? "ALL DISTINCT" : "");
    if (distinct == M) break;
  }
  return 0;
}
