/* Phi_t : GF(2)^{2t+1} -> GF(2), the rule-30 center cell after t steps as a function of x_{-t..t}.
   Variable x_p <-> input bit (p + t). Computes: ANF degree, number of ANF monomials, degree of
   Psi_t = Phi_t + x_{-t}, weight of Psi_t, Walsh max |W|, resiliency order, and the ANF
   degree of Phi_t restricted to the right part (x_{-t} = ... ) etc. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int main(int argc, char **argv) {
  int t = atoi(argv[1]); int n = 2 * t + 1; long M = 1L << n; long NW = M >= 64 ? M / 64 : 1;
  int ncell = 2 * t + 1;
  u64 **cur = malloc(ncell * sizeof(u64 *)), **nxt = malloc(ncell * sizeof(u64 *));
  for (int i = 0; i < ncell; i++) { cur[i] = calloc(NW, 8); nxt[i] = calloc(NW, 8); }
  /* projection truth tables: bit x of table for variable v is (x >> v) & 1 */
  for (int v = 0; v < n; v++) {
    for (long w = 0; w < NW; w++) {
      u64 word = 0;
      for (int b = 0; b < 64 && w * 64 + b < M; b++) if (((w * 64 + b) >> v) & 1) word |= 1ULL << b;
      cur[v][w] = word;
    }
  }
  /* cur[i] = cell(s, i - t) for i in [0, 2t]; at step s only i in [s, 2t - s] are needed */
  for (int s = 0; s < t; s++) {
    for (int i = s + 1; i <= 2 * t - s - 1; i++)
      for (long w = 0; w < NW; w++) nxt[i][w] = cur[i - 1][w] ^ (cur[i][w] | cur[i + 1][w]);
    for (int i = s + 1; i <= 2 * t - s - 1; i++) { u64 *tmp = cur[i]; cur[i] = nxt[i]; nxt[i] = tmp; }
  }
  u64 *f = cur[t];
  long wt = 0; for (long w = 0; w < NW; w++) wt += __builtin_popcountll(f[w]);
  /* Walsh transform */
  int *W = malloc(M * sizeof(int));
  for (long x = 0; x < M; x++) W[x] = ((f[x >> 6] >> (x & 63)) & 1) ? -1 : 1;
  for (int v = 0; v < n; v++) for (long x = 0; x < M; x++) if (!((x >> v) & 1)) { int a = W[x], b = W[x | (1L << v)]; W[x] = a + b; W[x | (1L << v)] = a - b; }
  long maxW = 0; int res = n; long maxWa = 0;
  for (long a = 0; a < M; a++) { long w = W[a] < 0 ? -W[a] : W[a]; if (w > maxW) { maxW = w; maxWa = a; } if (W[a] != 0) { int k = __builtin_popcountll(a); if (k - 1 < res) res = k - 1; } }
  /* W(0) != 0 would mean unbalanced: res = -1 */
  /* ANF via Moebius transform (in place on bits) */
  u64 *g = malloc(NW * 8); memcpy(g, f, NW * 8);
  for (int v = 0; v < n; v++) {
    if (v < 6) {
      u64 mask; int sh = 1 << v;
      static const u64 m[6] = {0x5555555555555555ULL, 0x3333333333333333ULL, 0x0F0F0F0F0F0F0F0FULL, 0x00FF00FF00FF00FFULL, 0x0000FFFF0000FFFFULL, 0x00000000FFFFFFFFULL};
      mask = m[v];
      for (long w = 0; w < NW; w++) g[w] ^= (g[w] & mask) << sh;
    } else {
      long st = 1L << (v - 6);
      for (long w = 0; w < NW; w++) if (!(w & st)) g[w | st] ^= g[w];
    }
  }
  int deg = 0; long nmon = 0; long degcount[64] = {0}; long topmon = -1;
  for (long x = 0; x < M; x++) if ((g[x >> 6] >> (x & 63)) & 1) { int k = __builtin_popcountll(x); nmon++; degcount[k]++; if (k > deg) { deg = k; topmon = x; } }
  printf("t=%d n=%d weight=%ld deg=%d monomials=%ld max|W|=%ld (at a=%lx) resiliency=%d\n", t, n, wt, deg, nmon, maxW, maxWa, res);
  printf("  monomials by degree:"); for (int k = 0; k <= deg; k++) printf(" %ld", degcount[k]); printf("\n");
  printf("  a top-degree monomial (positions):"); for (int v = 0; v < n; v++) if ((topmon >> v) & 1) printf(" %d", v - t); printf("\n");
  /* coefficient check: c(t) = coefficient of x_0 */
  long mono0 = 1L << t; printf("  coeff of x_0 = %d\n", (int)((g[mono0 >> 6] >> (mono0 & 63)) & 1));
  return 0;
}
