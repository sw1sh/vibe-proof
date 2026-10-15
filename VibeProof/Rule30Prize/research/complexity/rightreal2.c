// Right half columns 1..K driven by periodic word w at column 0, column K+1 free (existential).
// Output: column 1 at selected phases. Count realizable output words of length n (subset construction
// from all initial states), by DFS over words with state-set bitmaps.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int K, P, n; static int cw[64]; static int outph[64]; static int nout;
static int N;
static int step(int s, int c, int a) {
  int out = 0;
  for (int i = 0; i < K; i++) {
    int l = (i == 0) ? c : (s >> (i - 1)) & 1;
    int m = (s >> i) & 1;
    int r = (i == K - 1) ? a : (s >> (i + 1)) & 1;
    out |= (l ^ (m | r)) << i;
  }
  return out;
}
// transition over one period: from state s at phase 0, produce output bits at phases in outph, end state
// we enumerate all 2^P free-input choices.
static uint64_t *words; static long cnt[64];
static int W; // words of the state-set bitmap
static void dfs(uint64_t *S, int depth) {
  cnt[depth]++;
  if (depth == n) return;
  // for each output symbol (bit pattern over the nout phases of one period), compute successor set
  int nsym = 1 << nout;
  uint64_t *T = calloc((size_t)nsym * W, sizeof(uint64_t));
  for (int s = 0; s < N; s++) if (S[s >> 6] >> (s & 63) & 1) {
    for (int a = 0; a < (1 << P); a++) {
      int st = s, sym = 0, oi = 0;
      for (int ph = 0; ph < P; ph++) {
        // output col1 at this phase before stepping
        if (oi < nout && outph[oi] == ph) { sym |= (st & 1) << oi; oi++; }
        st = step(st, cw[ph], (a >> ph) & 1);
      }
      T[(size_t)sym * W + (st >> 6)] |= 1ULL << (st & 63);
    }
  }
  for (int sym = 0; sym < nsym; sym++) {
    uint64_t *TS = T + (size_t)sym * W; int nz = 0;
    for (int i = 0; i < W; i++) if (TS[i]) { nz = 1; break; }
    if (nz) dfs(TS, depth + 1);
  }
  free(T);
}
int main(int argc, char **argv) {
  const char *w = argv[1]; K = atoi(argv[2]); n = atoi(argv[3]); const char *ph = argv[4];
  P = strlen(w); for (int i = 0; i < P; i++) cw[i] = w[i] - '0';
  nout = 0; for (int i = 0; ph[i]; i++) outph[nout++] = ph[i] - '0';
  N = 1 << K; W = (N + 63) / 64;
  uint64_t *S = calloc(W, sizeof(uint64_t)); for (int s = 0; s < N; s++) S[s >> 6] |= 1ULL << (s & 63);
  dfs(S, 0);
  printf("w=%s K=%d outphases=%s:", w, K, ph);
  for (int d = 1; d <= n; d++) printf(" %ld", cnt[d]); printf("\n");
  return 0;
}
