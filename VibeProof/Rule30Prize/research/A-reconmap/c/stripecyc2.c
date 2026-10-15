/* Even-phase stripe tail: cells >= K (K even) follow black-at-even-positions; cell K = 1.
   Inner cells 1..K-1, wall 0 at cell 0, cell K = 1 forever (confinement).  Count all cycles. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int K;
static inline uint32_t stepw(uint32_t v) {
  int n = K - 1;
  uint64_t ext = ((uint64_t)v << 1) | ((uint64_t)1 << K);
  uint64_t nw = (ext >> 1) ^ (ext | (ext << 1));
  return (uint32_t)((nw >> 1) & ((1ULL << n) - 1));
}
int main(int argc, char **argv) {
  K = atoi(argv[1]);
  int n = K - 1; uint32_t N = 1u << n;
  uint8_t *col = calloc(N, 1); uint32_t *path = malloc(sizeof(uint32_t) * (N + 1));
  long cycles = 0;
  for (uint32_t s = 0; s < N; s++) {
    if (col[s]) continue;
    int len = 0; uint32_t v = s;
    while (!col[v]) { col[v] = 1; path[len++] = v; v = stepw(v); }
    if (col[v] == 1) {
      int st = 0; while (path[st] != v) st++;
      int p = len - st; cycles++;
      printf("K=%d cycle length %d:", K, p);
      for (int j = 0; j < p && j < 3; j++) { printf(" "); for (int i = 0; i < n; i++) putchar((path[st + j] >> i) & 1 ? '1' : '0'); }
      printf("\n");
    }
    for (int i = 0; i < len; i++) col[path[i]] = 2;
  }
  printf("K=%d: %ld cycles\n", K, cycles);
  return 0;
}
