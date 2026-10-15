// Independent check of the black-shield thresholds.
// Row bit i = cell at column m+1+i at time t. Column m is black (1) at times t..t+K-1.
// Step: new_i = left_i xor (cell_i or right_i), left_0 = 1 (column m).
// After K steps, bits 0..n-1 are exact when the initial row has W = K+n bits.
// Usage: shieldk K n full        -> enumerate all 2^(K+n) rows
//        shieldk K n rand N seed -> sample N random rows
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t s[2];
static inline uint64_t rotl(const uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t next(void) { // xoroshiro128+
  const uint64_t s0 = s[0]; uint64_t s1 = s[1]; const uint64_t r = s0 + s1;
  s1 ^= s0; s[0] = rotl(s0, 55) ^ s1 ^ (s1 << 14); s[1] = rotl(s1, 36); return r; }
int main(int argc, char **argv) {
  int K = atoi(argv[1]), n = atoi(argv[2]);
  int W = K + n;
  uint64_t mask = (W >= 64) ? ~0ULL : ((1ULL << W) - 1);
  uint64_t outmask = (1ULL << n) - 1;
  static uint64_t hist[1 << 12]; memset(hist, 0, sizeof hist);
  uint64_t witness[1 << 12]; memset(witness, 0, sizeof witness);
  int full = strcmp(argv[3], "full") == 0;
  uint64_t N = full ? (1ULL << W) : strtoull(argv[4], 0, 10);
  if (!full) { s[0] = strtoull(argv[5], 0, 10) * 0x9E3779B97F4A7C15ULL + 1; s[1] = 0xD1B54A32D192ED03ULL; }
  for (uint64_t X = 0; X < N; X++) {
    uint64_t row = full ? X : (next() & mask);
    uint64_t r0 = row;
    for (int k = 0; k < K; k++) row = (((row << 1) | 1) ^ (row | (row >> 1))) & mask;
    uint64_t o = row & outmask;
    if (hist[o] == 0) witness[o] = r0;
    hist[o]++;
  }
  printf("K=%d n=%d W=%d %s N=%llu\n", K, n, W, full ? "full" : "rand", (unsigned long long)N);
  for (uint64_t o = 0; o <= outmask; o++) if (hist[o]) {
    printf("  cells m+1..m+%d = ", n);
    for (int i = 0; i < n; i++) putchar(((o >> i) & 1) ? '1' : '0');
    printf("  count=%llu  witness_row(bit i = col m+1+i)=0x%llx\n", (unsigned long long)hist[o], (unsigned long long)witness[o]);
  }
  return 0;
}
