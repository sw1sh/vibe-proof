// Left half of rule 30 (positions -1,-2,...) driven by periodic boundary c = w^inf at position 0.
// State: bit i <-> position -(i+1).  new_i = old_{i+1} ^ (old_i | old_{i-1}), old_{-1} = c(t).
// Constraint A (column-0 consistency, uses only left half): c(t)=1  =>  col_{-1}(t) = !c(t+1).
// Constraint B (column-1 rule, any right half): col1(t) prescribed = c(t+1)^col_{-1}(t) when c(t)=0;
//   col1(t)=1 => col1(t+1) = !c(t).  Greedy check (free col1 values set to 0).
// For every x with support in [-L,-1], report survival = first violating time (relative to T).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: w L maxsteps [useB]\n"); return 1; }
  const char *w = argv[1]; int P = strlen(w); int L = atoi(argv[2]); int MS = atoi(argv[3]);
  int useB = argc > 4 ? atoi(argv[4]) : 1;
  if (L + MS + 2 > 127) { fprintf(stderr, "too wide\n"); return 1; }
  int cw[1024]; for (int i = 0; i < P; i++) cw[i] = w[i] - '0';
  long hist[1024]; memset(hist, 0, sizeof hist);
  int best = -1; uint64_t bestx = 0; int bestph = 0;
  for (int ph = 0; ph < P; ph++) {
    for (uint64_t x = 0; x < (1ULL << L); x++) {
      u128 row = (u128)x; int surv = MS;
      int col1prev = 0, col1prevKnown = 1; // before T: treat as unconstrained: col1prev=0 means no forcing
      int first = 1;
      for (int t = 0; t < MS; t++) {
        int c = cw[(ph + t) % P], cn = cw[(ph + t + 1) % P];
        int m1 = (int)(row & 1);
        // constraint A
        if (c == 1 && m1 != !cn) { surv = t; break; }
        // constraint B
        if (useB) {
          int v; int forced = (!first && col1prev == 1);
          int forcedval = forced ? !cw[(ph + t - 1) % P] : -1;
          if (c == 0) {
            v = cn ^ m1;
            if (forced && v != forcedval) { surv = t; break; }
          } else {
            v = forced ? forcedval : 0;
          }
          col1prev = v; first = 0;
        }
        // evolve
        u128 right = (row << 1) | (u128)c;   // old_{i-1}
        u128 left = row >> 1;                 // old_{i+1}
        row = left ^ (row | right);
        u128 mask = (((u128)1) << (L + t + 2)) - 1; row &= mask;
      }
      hist[surv]++;
      if (surv > best) { best = surv; bestx = x; bestph = ph; }
    }
  }
  printf("w=%s L=%d maxsteps=%d useB=%d: best survival %d (x=%llx phase %d)\n", w, L, MS, useB, best, (unsigned long long)bestx, bestph);
  printf("hist tail:"); for (int s = MS; s >= 0 && s >= best - 12; s--) if (hist[s]) printf(" %d:%ld", s, hist[s]); printf("\n");
  return 0;
}
