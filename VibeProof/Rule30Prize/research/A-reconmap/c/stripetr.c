/* For rule 30 ZBL with cells 1..K-1 free, cell 0 = 0, cell K = 1 (stripe beyond), compute the maximum
   number of steps to reach the stripe fixed point, over all 2^(K-1) initial inner states. */
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
  uint32_t S = 0; for (int i = 1; i <= n; i++) if (i % 2 == 1) S |= 1u << (i - 1);
  if (stepw(S) != S) { printf("stripe not fixed?\n"); return 1; }
  /* depth via memo: dist[v] = steps to reach S; compute iteratively with path following */
  uint16_t *dist = malloc(sizeof(uint16_t) * N);
  for (uint32_t i = 0; i < N; i++) dist[i] = 0xFFFF;
  dist[S] = 0;
  uint32_t *path = malloc(sizeof(uint32_t) * 70000);
  int maxd = 0; uint32_t arg = 0;
  for (uint32_t s = 0; s < N; s++) {
    int len = 0; uint32_t v = s;
    while (dist[v] == 0xFFFF) { path[len++] = v; v = stepw(v); if (len > 65000) { printf("long path\n"); return 1; } }
    int d = dist[v];
    for (int i = len - 1; i >= 0; i--) { d++; dist[path[i]] = d; }
    if (dist[s] > maxd) { maxd = dist[s]; arg = s; }
  }
  printf("K=%d: max steps to reach the stripe = %d (from ", K, maxd);
  for (int i = 0; i < n; i++) putchar((arg >> i) & 1 ? '1' : '0');
  printf(")\n");
  return 0;
}
