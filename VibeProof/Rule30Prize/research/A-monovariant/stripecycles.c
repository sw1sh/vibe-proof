// States: prefixes P = (x_1..x_{M}) with the stripe beyond (x_k = [k odd] for k > M). By agrees_two_steps,
// Z^2 maps such configs to such configs (same M). Find all cycles of Z^2 on states satisfying the phase-0 constraint
// (x_1 = 1 at even times). Report cycles other than the stripe.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static inline u128 step(u128 r) { return (r >> 1) ^ (r | (r << 1)); }
int main(int argc, char **argv) {
  int M = atoi(argv[1]);
  u128 S = 0; for (int i = 0; i < 120; i += 2) S |= (u128)1 << i;   // stripe: bit i = x_{i+1}, x odd -> bit even
  uint64_t N = 1ull << M;
  uint32_t *next = malloc(sizeof(uint32_t) * N);
  unsigned char *alive = malloc(N);
  u128 hiS = S & ~((((u128)1) << M) - 1);   // stripe beyond M (bits >= M)
  for (uint64_t P = 0; P < N; P++) {
    u128 r = (u128)P | hiS;
    // window: keep 120 bits; after 2 steps bits up to ~117 valid
    u128 r1 = step(r), r2 = step(r1);
    int ok = (r & 1) && (r2 & 1);
    // check agreement beyond M (sanity)
    u128 mask = ((((u128)1) << 110) - 1) & ~((((u128)1) << M) - 1);
    if (((r2 ^ S) & mask) != 0) { printf("T3 violated?? P=%llu\n", (unsigned long long)P); return 1; }
    next[P] = (uint32_t)(r2 & (N - 1));
    alive[P] = ok;
  }
  // states with infinite constrained future = those on or leading into cycles within alive states; find cycles
  unsigned char *col = calloc(N, 1);
  long ncyc = 0, nontriv = 0;
  for (uint64_t P = 0; P < N; P++) {
    if (col[P] || !alive[P]) continue;
    // walk
    uint64_t q = P;
    while (alive[q] && col[q] == 0) { col[q] = 1; q = next[q]; }
    if (alive[q] && col[q] == 1) {
      // found a cycle through q (newly visited in this walk)
      ncyc++;
      uint64_t c = q; int len = 0; int stripe = 1;
      do { if (c != (S & (N - 1))) stripe = 0; len++; c = next[c]; } while (c != q);
      if (!stripe) {
        nontriv++;
        printf("nonstripe cycle len %d through P=", len);
        for (int i = 0; i < M; i++) putchar(((q >> i) & 1) ? '1' : '0');
        // print f along the cycle: x_1 at the odd time between = step(r)_1
        printf("  f-cycle=");
        c = q;
        do { u128 r = (u128)c | hiS; putchar((step(r) & 1) ? '1' : '0'); c = next[c]; } while (c != q);
        printf("\n");
      }
    }
    // mark the walk as finished
    q = P;
    while (alive[q] && col[q] == 1) { col[q] = 2; q = next[q]; }
  }
  printf("M=%d: cycles among constrained states: %ld, non-stripe: %ld\n", M, ncyc, nontriv);
}
