/* Cycles of the ZBL restricted to rows equal to the stripe beyond an odd position K:
   inner cells 1..K-1 free, cell K = 1 (stripe), cells > K stripe (do not matter for the inner update
   since cell K is black: the inner update at K-1 sees v(K) = 1).  Enumerate all 2^(K-1) inner states,
   find all cycles, and report cycles whose trace (cell 1) is black at all even times along the cycle
   for some phase (i.e. the cycle has even length p and cell 1 is black at times 0,2,4,... for a suitable start). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int K;
static inline uint32_t stepw(uint32_t v) {
  /* bit i-1 <-> cell i, i = 1..K-1 ; cell 0 = 0, cell K = 1 */
  int n = K - 1;
  uint64_t ext = ((uint64_t)v << 1) | ((uint64_t)1 << K);   /* bit i <-> cell i, i=0..K */
  uint64_t right = ext >> 1, left = ext << 1;               /* right[i] = cell i+1, left[i] = cell i-1 */
  uint64_t nw = right ^ (ext | left);
  return (uint32_t)((nw >> 1) & ((1ULL << n) - 1));
}
int main(int argc, char **argv) {
  K = atoi(argv[1]);
  int n = K - 1; uint32_t N = 1u << n;
  uint8_t *col = calloc(N, 1);   /* 0 unvisited, 1 on stack, 2 done */
  uint32_t *path = malloc(sizeof(uint32_t) * (N + 1));
  long cycles = 0, good = 0;
  for (uint32_t s = 0; s < N; s++) {
    if (col[s]) continue;
    int len = 0; uint32_t v = s;
    while (!col[v]) { col[v] = 1; path[len++] = v; v = stepw(v); }
    if (col[v] == 1) {
      /* cycle found: from position of v in path */
      int st = 0; while (path[st] != v) st++;
      int p = len - st;
      cycles++;
      /* check: exists phase r such that p even and cell 1 black at path[st + (r + 2j) % p] for all j */
      int ok = 0;
      if (p % 2 == 0) {
        for (int r = 0; r < 2 && !ok; r++) {
          int all = 1;
          for (int j = r; j < p; j += 2) if (!(path[st + j] & 1)) { all = 0; break; }
          if (all) ok = 1;
        }
      } else {
        int all = 1; for (int j = 0; j < p; j++) if (!(path[st + j] & 1)) { all = 0; break; }
        ok = all;
      }
      if (ok) {
        good++;
        if (good <= 6) {
          printf("K=%d cycle length %d constrained; states:", K, p);
          for (int j = 0; j < p && j < 4; j++) { printf(" "); for (int i = 0; i < n; i++) putchar((path[st + j] >> i) & 1 ? '1' : '0'); }
          printf("\n");
        }
      }
    }
    for (int i = 0; i < len; i++) col[path[i]] = 2;
  }
  printf("K=%d: %ld cycles, %ld satisfy the period-2 constraint\n", K, cycles, good);
  return 0;
}
