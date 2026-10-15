// Right half strip (columns 1..b), driven at column 0 by c(t) = 1 at even t, 0 at odd t; free input at column b+1.
// Question: can column 1 be white at K consecutive odd times (t0, t0+2, ..., t0+2K-2) for some strip state and inputs?
// Reachable set of strip states is all states (start anywhere), so search: S_0 = all states at an odd time;
// require col1 = 0 at that time; evolve 2 steps with all inputs; require col1 = 0 again; ...
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv){
  int K = atoi(argv[1]);
  for (int b = 2; b <= 22; b++){
    uint32_t N = 1u << b, M = N - 1;
    uint8_t *cur = malloc(N), *nxt = malloc(N);
    // bit i <-> column i+1. new(j) = old(j-1) xor (old(j) | old(j+1)); old(0) = c(t), old(b+1) = input
    for (uint32_t s = 0; s < N; s++) cur[s] = !(s & 1);   // at odd time t0, col1 = 0
    int alive = 1;
    for (int k = 1; k < K && alive; k++){
      memset(nxt, 0, N);
      for (uint32_t s = 0; s < N; s++) if (cur[s]) {
        for (int v1 = 0; v1 < 2; v1++){
          // step at odd time: c = 0
          uint32_t full = s | ((uint32_t)v1 << b);
          uint32_t left = (full << 1) | 0u;      // old(j-1) at bit j-1 position -> shift
          uint32_t s1 = ((left) ^ (full | (full >> 1))) & M;
          for (int v2 = 0; v2 < 2; v2++){
            uint32_t full2 = s1 | ((uint32_t)v2 << b);
            uint32_t left2 = (full2 << 1) | 1u;  // even time: c = 1
            uint32_t s2 = ((left2) ^ (full2 | (full2 >> 1))) & M;
            if (!(s2 & 1)) nxt[s2] = 1;
          }
        }
      }
      alive = 0; for (uint32_t s = 0; s < N; s++) if (nxt[s]) { alive = 1; break; }
      uint8_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long cnt = 0; for (uint32_t s = 0; s < N; s++) cnt += cur[s];
    printf("b=%d: K=%d consecutive white col1 at odd times possible? %s (%ld states)\n", b, K, alive ? "yes" : "NO", cnt);
    fflush(stdout);
    free(cur); free(nxt);
    if (!alive) break;
  }
  return 0;
}
