/* Right diagonals R_j(t) = cell(t, t-j) of rule 30 on t in [0, 2^E): R_j(t+1) = R_j(t) ^ (R_{j-1}(t) | R_{j-2}(t)).
   For each j: least period 2^{e_j}; Mahler coefficients a_{j,m} = sum_{k subset m} R_j(k) (mod 2) over one period;
   L_j = 1 + max{m : a_{j,m} = 1} (linear complexity), and bit-degree = max popcount(m) with a_{j,m} = 1. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  int J = atoi(argv[1]), E = atoi(argv[2]); long N = 1L << E;
  unsigned char *p2 = calloc(N, 1), *p1 = malloc(N), *cur = malloc(N), *a = malloc(N);
  memset(p1, 1, N);  /* R_0 = 1, R_{-1} = 0 */
  for (int j = 1; j <= J; j++) {
    unsigned char x = 0;
    for (long t = 0; t < N; t++) { cur[t] = x; x ^= (p1[t] | p2[t]); }
    /* least period (power of 2) */
    long P = 1; while (P < N) { long t; for (t = 0; t + P < N; t++) if (cur[t] != cur[t + P]) break; if (t + P >= N) break; P *= 2; }
    if (P >= N) { printf("j=%d period >= 2^%d, stop\n", j, E); break; }
    memcpy(a, cur, P);
    for (long b = 1; b < P; b <<= 1) for (long m = 0; m < P; m++) if (m & b) a[m] ^= a[m ^ b];
    long top = -1; int bdeg = 0; long nz = 0;
    for (long m = 0; m < P; m++) if (a[m]) { top = m; nz++; int pc = __builtin_popcountl(m); if (pc > bdeg) bdeg = pc; }
    int e = __builtin_ctzl(P);
    printf("j=%2d e_j=%2d L_j=%7ld  (2^(e-1)=%ld)  L_j/2^e=%.3f  bitdeg=%d  #nonzero Mahler=%ld\n", j, e, top + 1, P / 2, (double)(top + 1) / P, bdeg, nz);
    unsigned char *tmp = p2; p2 = p1; p1 = cur; cur = tmp;
  }
  return 0;
}
