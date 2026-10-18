#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
// For a fixed input u (column 0 over n times) and all right halves r on sites 1..n,
// count distinct prefixes v(0..t) of column 1 for each t: the branching profile.
int main(void) {
  int n = 18;
  srand(12345);
  for (int trial = 0; trial < 6; trial++) {
    uint32_t u = 0;
    for (int t = 0; t < n; t++) if (rand() & 1) u |= 1u << t;
    if (trial == 0) u = 0x2AAAA & ((1u << n) - 1);   // alternating input
    int cnt[64] = {0};
    // sets of prefixes per length: use a hash via sorting
    static uint32_t vs[1 << 18];
    for (uint32_t r = 0; r < (1u << n); r++) {
      // cells 0..n+1: cell 0 is the boundary (input), cells 1..n the right half, beyond 0
      uint64_t y = ((uint64_t)r) << 1;   // bit i = site i
      uint32_t v = 0;
      for (int t = 0; t < n; t++) {
        y = (y & ~1ULL) | ((u >> t) & 1);       // boundary input at site 0
        v |= (uint32_t)((y >> 1) & 1) << t;     // output: site 1
        uint64_t ny = ((y << 1) ^ (y | (y >> 1)));
        y = ny & ((1ULL << (n + 2)) - 1);
      }
      vs[r] = v;
    }
    printf("u=");
    for (int t = 0; t < n; t++) printf("%d", (u >> t) & 1);
    printf("  distinct prefixes by length:");
    for (int len = 1; len <= n; len++) {
      uint32_t mask = (len == 32) ? ~0u : ((1u << len) - 1);
      // count distinct (vs & mask)
      static uint8_t seen[1 << 18];
      for (uint32_t k = 0; k < (1u << len); k++) seen[k] = 0;
      int c = 0;
      for (uint32_t r = 0; r < (1u << n); r++) { uint32_t p = vs[r] & mask; if (!seen[p]) { seen[p] = 1; c++; } }
      printf(" %d", c);
    }
    printf("\n");
  }
  return 0;
}
