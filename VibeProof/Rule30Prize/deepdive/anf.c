/* anf.c — the reconstruction map Θ of the constrained zero-boundary left half, symbolically.
 *
 * Left half in depth coordinates, wall at depth 0 (the effective boundary under alternation).
 * Column 1 (= cell column -1) is 1 at even times and the free bit f_s at time 2s+1.
 * Deeper columns follow sideways: X_{k+1}(t) = X_k(t+1) XOR (X_k(t) OR X_{k-1}(t)), X_0 = 0.
 * The time-0 row is y_0(k) = X_k(0), a Boolean function of f_0, f_1, ...
 * Every cell is a truth table over m free bits (bit-sliced); the program prints, for each depth
 * k, the variables the row cell depends on, its algebraic degree and its number of monomials.
 *
 * usage: anf m      (m <= 20 free bits; depths up to 2m+1)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
static int m; static long NW; /* words per truth table */

static u64 *tt_new(void) { return calloc(NW, 8); }
static void tt_var(u64 *a, int v) { /* truth table of f_v */
  for (long i = 0; i < NW; i++) {
    u64 w = 0;
    for (int b = 0; b < 64; b++) { long x = i * 64 + b; if ((x >> v) & 1) w |= 1ULL << b; }
    a[i] = w;
  }
}
static void tt_const(u64 *a, int c) { memset(a, c ? 0xff : 0, NW * 8); }

/* Moebius transform in place (truth table -> ANF coefficients) */
static void mobius(u64 *a) {
  for (int v = 0; v < m; v++) {
    if (v < 6) {
      static const u64 mask[6] = {0x5555555555555555ULL, 0x3333333333333333ULL, 0x0f0f0f0f0f0f0f0fULL,
                                  0x00ff00ff00ff00ffULL, 0x0000ffff0000ffffULL, 0x00000000ffffffffULL};
      int s = 1 << v;
      for (long i = 0; i < NW; i++) a[i] ^= (a[i] & mask[v]) << s;
    } else {
      long s = 1L << (v - 6);
      for (long i = 0; i < NW; i++) if (i & s) a[i] ^= a[i ^ s];
    }
  }
}

int main(int argc, char **argv) {
  m = argc > 1 ? atoi(argv[1]) : 14;
  long N = 1L << m; NW = N / 64 > 0 ? N / 64 : 1;
  int K = 2 * m + 1, T = 2 * m + 2;
  /* X[k][t] truth tables; only previous two columns kept */
  u64 **Xm = malloc((T + 1) * sizeof(u64 *)), **X0 = malloc((T + 1) * sizeof(u64 *)),
      **X1 = malloc((T + 1) * sizeof(u64 *));
  for (int t = 0; t <= T; t++) { Xm[t] = tt_new(); X0[t] = tt_new(); X1[t] = tt_new(); }
  /* X_0 = wall = 0 (Xm), X_1 = column 1 */
  for (int t = 0; t <= T; t++) {
    tt_const(Xm[t], 0);
    if (t % 2 == 0) tt_const(X0[t], 1);
    else if ((t - 1) / 2 < m) tt_var(X0[t], (t - 1) / 2);
    else tt_const(X0[t], 0); /* beyond m free bits: unused region */
  }
  u64 *buf = tt_new();
  printf(" k  deg  #monomials  depends-on (f indices)\n");
  for (int k = 1; k <= K; k++) {
    /* report y_0(k) = X_k(0), held in X0[0] */
    memcpy(buf, X0[0], NW * 8);
    mobius(buf);
    long mons = 0; int deg = 0; unsigned long used = 0;
    for (long x = 0; x < N; x++)
      if ((buf[x >> 6] >> (x & 63)) & 1) { mons++; int d = __builtin_popcountl(x); if (d > deg) deg = d; used |= x; }
    printf("%2d  %3d  %10ld  ", k, deg, mons);
    for (int v = 0; v < m; v++) if ((used >> v) & 1) printf("%d ", v);
    printf("\n");
    /* next column: X_{k+1}(t) = X_k(t+1) ^ (X_k(t) | X_{k-1}(t)), valid t <= T - k */
    for (int t = 0; t + 1 <= T - k; t++)
      for (long i = 0; i < NW; i++) X1[t][i] = X0[t + 1][i] ^ (X0[t][i] | Xm[t][i]);
    u64 **tmp = Xm; Xm = X0; X0 = X1; X1 = tmp;
  }
  return 0;
}
