// Monovariant battery: for every finite config of width <= W (bit 0 = x_1 = 1), follow the phase-0 constrained
// history; for every surviving 2-step transition (even t -> t+2) record min/max of Delta Q for many quantities Q,
// together with max Q / w (w = cone width W + t).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static inline u128 step(u128 r) { return (r >> 1) ^ (r | (r << 1)); }
static inline int pc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; if (lo) return __builtin_ctzll(lo); return 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
#define NQ 16
const char *names[NQ] = {"weight","walls","walls00","walls11","walls_class1","walls_class0","firstdef",
  "defects_vs_stripe","runs_of_ones","weight_odd_pos","weight_even_pos","firstwall_class1_pos","defects_class1",
  "zero_runs","ones_pairs11","pattern_101"};
static u128 ALT0, ALT1, STRIPE;
static void quantities(u128 r, int w, int t, int *q) {
  u128 mask = (w >= 128) ? ~(u128)0 : ((((u128)1) << w) - 1);
  u128 sh = (r << 1) & mask;               // bit i = x_i (x_0 = 0)
  u128 eq = ~(r ^ sh) & mask;              // wall at k=i+1
  u128 w00 = ~r & ~sh & mask, w11 = r & sh & mask;
  u128 cls1 = (t & 1) ? ALT1 : ALT0;      // bits i with (i+1+t) odd
  cls1 &= mask;
  u128 def = (r ^ STRIPE) & mask;
  q[0] = pc(r & mask);
  q[1] = pc(eq);
  q[2] = pc(w00);
  q[3] = pc(w11);
  q[4] = pc(eq & cls1);
  q[5] = pc(eq & ~cls1 & mask);
  q[6] = def ? ctz128(def) + 1 : 999;
  q[7] = pc(def);
  q[8] = pc(r & ~sh & mask);               // starts of runs of ones (x_k=1, x_{k-1}=0)
  q[9] = pc(r & STRIPE & mask);            // ones at odd k (bit even)
  q[10] = pc(r & ~STRIPE & mask);
  u128 e1 = eq & cls1; q[11] = e1 ? ctz128(e1) + 1 : 999;
  q[12] = pc(def & cls1);
  q[13] = pc(~r & sh & mask);              // starts of zero runs inside cone (x_k=0,x_{k-1}=1)
  q[14] = pc(w11);
  q[15] = pc(r & ~(r << 1) & (r << 2) & ~(r >> 0 ^ r) & mask); // placeholder (same as weight of pattern 1?1)
}
int main(int argc, char **argv) {
  int Wmax = atoi(argv[1]);
  ALT0 = 0; ALT1 = 0; STRIPE = 0;
  for (int i = 0; i < 128; i++) { if (i % 2 == 0) STRIPE |= (u128)1 << i; }
  // class-1 bits: (i+1+t) odd. For t even: i even -> ALT0 = bits i even. For t odd: i odd.
  for (int i = 0; i < 128; i++) { if (i % 2 == 0) ALT0 |= (u128)1 << i; else ALT1 |= (u128)1 << i; }
  int mind[NQ], maxd[NQ]; double maxratio[NQ], minratio[NQ];
  for (int j = 0; j < NQ; j++) { mind[j] = 1 << 30; maxd[j] = -(1 << 30); maxratio[j] = -1e9; minratio[j] = 1e9; }
  long ntrans = 0;
  for (int W = 1; W <= Wmax; W++) {
    for (uint64_t L = 1ull << (W - 1); L < (1ull << W); L++) {
      if (!(L & 1)) continue;
      u128 r = L; int t = 0;
      int qa[NQ], qb[NQ];
      quantities(r, W, 0, qa);
      while (1) {
        u128 r1 = step(r), r2 = step(r1);
        if (!(r2 & 1)) break;               // dies at t+2
        if (W + t + 2 > 120) break;
        quantities(r2, W + t + 2, t + 2, qb);
        for (int j = 0; j < NQ; j++) {
          if (qa[j] == 999 || qb[j] == 999) continue;
          int d = qb[j] - qa[j];
          if (d < mind[j]) mind[j] = d;
          if (d > maxd[j]) maxd[j] = d;
          double rt = (double)qa[j] / (W + t);
          if (rt > maxratio[j]) maxratio[j] = rt;
          if (rt < minratio[j]) minratio[j] = rt;
        }
        ntrans++;
        memcpy(qa, qb, sizeof qa);
        r = r2; t += 2;
      }
    }
  }
  printf("transitions: %ld (widths <= %d)\n", ntrans, Wmax);
  for (int j = 0; j < NQ - 1; j++) printf("%-22s  Delta in [%4d,%4d]   Q/w in [%.3f, %.3f]\n", names[j], mind[j], maxd[j], minratio[j], maxratio[j]);
}
