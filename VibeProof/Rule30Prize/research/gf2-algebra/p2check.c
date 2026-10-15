/* Enumerate all rule-30 space-time patches on columns [-6, 3], times [0, 6], i.e. initial row (10 cells)
   plus the two boundary columns at times 1..6 (free), interior computed by the rule. Keep patches whose
   column 0 is 1 at even times and 0 at odd times. Check: column -4 at odd times t in [1,3]
   (where the derivation's cells stay inside the computed region) is always 0, and record which other
   (column, time) cells are forced. */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  const int PL = -6, PR = 3, W = PR - PL + 1, TT = 7;
  long kept = 0; int forced1[TT][W], forced0[TT][W];
  for (int t = 0; t < TT; t++) for (int i = 0; i < W; i++) forced1[t][i] = forced0[t][i] = 1;
  for (long code = 0; code < (1L << (W + 2 * (TT - 1))); code++) {
    int g[TT][W]; long c = code;
    for (int i = 0; i < W; i++) { g[0][i] = c & 1; c >>= 1; }
    for (int t = 1; t < TT; t++) {
      g[t][0] = c & 1; c >>= 1; g[t][W - 1] = c & 1; c >>= 1;
      for (int i = 1; i < W - 1; i++) g[t][i] = g[t - 1][i - 1] ^ (g[t - 1][i] | g[t - 1][i + 1]);
    }
    int ok = 1;
    for (int t = 0; t < TT && ok; t++) if (g[t][0 - PL] != (t % 2 == 0)) ok = 0;
    if (!ok) continue;
    kept++;
    for (int t = 0; t < TT; t++) for (int i = 0; i < W; i++) { if (g[t][i]) forced0[t][i] = 0; else forced1[t][i] = 0; }
  }
  printf("patches with alternating center: %ld\n", kept);
  for (int t = 0; t < TT; t++) { printf("t=%d: ", t); for (int i = 0; i < W; i++) printf("%c", forced0[t][i] ? '0' : forced1[t][i] ? '1' : '.'); printf("   (columns %d..%d)\n", PL, PR); }
  return 0;
}
