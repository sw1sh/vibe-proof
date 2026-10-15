// DFS over left-finite left halves x (support in [-L,-1]) satisfying constraint A on [T, T+L),
// then forward simulation to the first violation of A. Reports max survival and count of survivors.
// bit i of x <-> position -(i+1). col_{-1}(T+n-1) depends only on x bits 0..n-1, and is permutive in bit n-1.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int P, L, MS; static int cw[64];
static long nleaves = 0; static int best = -1; static u128 bestx; static int bestph;
static long hist[512];
static int cval(int ph, int t) { return cw[(ph + t) % P]; }
static int col_m1_at(u128 x, int ph, int steps) { // col_{-1} after 'steps' steps
  u128 row = x;
  for (int t = 0; t < steps; t++) {
    int c = cval(ph, t);
    u128 right = (row << 1) | (u128)c; u128 left = row >> 1;
    row = left ^ (row | right);
  }
  return (int)(row & 1);
}
static void leaf(u128 x, int ph) {
  nleaves++;
  u128 row = x; int surv = MS;
  for (int t = 0; t < MS; t++) {
    int c = cval(ph, t), cn = cval(ph, t + 1);
    if (c == 1 && (int)(row & 1) != !cn) { surv = t; break; }
    u128 right = (row << 1) | (u128)c; u128 left = row >> 1;
    row = left ^ (row | right);
    if (L + t + 2 < 128) row &= ((((u128)1) << (L + t + 2)) - 1);
  }
  hist[surv]++;
  if (surv > best) { best = surv; bestx = x; bestph = ph; }
}
static void dfs(u128 x, int n, int ph) { // bits 0..n-1 chosen; choose bit n (position -(n+1)), controls col_{-1}(T+n)
  if (n == L) { leaf(x, ph); return; }
  int t = n; int c = cval(ph, t), cn = cval(ph, t + 1);
  int v0 = col_m1_at(x, ph, t);           // with bit n = 0
  if (c == 1) { int need = !cn; dfs(v0 == need ? x : (x | ((u128)1 << n)), n + 1, ph); }
  else { dfs(x, n + 1, ph); dfs(x | ((u128)1 << n), n + 1, ph); }
}
int main(int argc, char **argv) {
  const char *w = argv[1]; P = strlen(w); L = atoi(argv[2]); MS = atoi(argv[3]);
  for (int i = 0; i < P; i++) cw[i] = w[i] - '0';
  if (L + MS + 2 > 127) { fprintf(stderr, "too wide\n"); return 1; }
  for (int ph = 0; ph < P; ph++) dfs(0, 0, ph);
  printf("w=%s L=%d: leaves=%ld best survival=%d (ph %d)  survival/L=%.2f\n", w, L, nleaves, best, bestph, (double)best / L);
  printf("  tail:"); for (int s = MS; s >= 0 && s >= best - 8; s--) if (hist[s]) printf(" %d:%ld", s, hist[s]); printf("\n");
  return 0;
}
