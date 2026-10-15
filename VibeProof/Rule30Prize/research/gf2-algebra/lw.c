/* Leftward (rotated) rule 30 from boundary L_0 = 0, L_1 = w (w in GF(2)^m):
   L_{k+2}(s) = L_k(s+1) ^ (L_{k+1}(s) | L_k(s)).  X(w) = L_{2m}(0).
   Prints weight of X over all w, and also weight of Psi_t restricted etc. Bit-sliced over w. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int main(int argc, char **argv) {
  int M = atoi(argv[1]);
  for (int m = 1; m <= M; m++) {
    long N = 1L << m; long NW = N >= 64 ? N / 64 : 1;
    /* tables: Lk[s] for s in [0, m) ; keep three layers */
    u64 **A = malloc(m * sizeof(u64*)), **B = malloc(m * sizeof(u64*)), **C = malloc(m * sizeof(u64*));
    for (int s = 0; s < m; s++) { A[s] = calloc(NW, 8); B[s] = calloc(NW, 8); C[s] = calloc(NW, 8); }
    /* A = L_0 = 0, B = L_1 = w_s */
    for (int s = 0; s < m; s++) for (long x = 0; x < N; x++) if ((x >> s) & 1) B[s][x >> 6] |= 1ULL << (x & 63);
    if (N < 64) { /* mask unused bits */ }
    /* iterate k from 0: L_{k+2}(s) for s with s+1 < m (needs L_k(s+1)); domain shrinks: L_k defined on s <= m-1-floor((k-1)/2) roughly */
    int len0 = m, len1 = m; /* valid lengths of L_k and L_{k+1} */
    for (int k = 0; k + 2 <= 2 * m; k++) {
      /* L_{k+2}(s) = L_k(s+1) ^ (L_{k+1}(s) | L_k(s)); for L_0 = 0 we treat L_0(s+1) as 0 for all s < m (apex v = 0) */
      int len2 = (k == 0) ? m : (len0 - 1 < len1 ? len0 - 1 : len1);
      for (int s = 0; s < len2; s++) for (long q = 0; q < NW; q++) {
        u64 lk1 = (k == 0) ? 0 : A[s + 1][q];
        C[s][q] = lk1 ^ (B[s][q] | A[s][q]);
      }
      u64 **T = A; A = B; B = C; C = T; len0 = len1; len1 = len2;
    }
    /* now B = L_{2m}, at s = 0 */
    long wt = 0; for (long q = 0; q < NW; q++) { u64 v = B[0][q]; if (N < 64) v &= (1ULL << N) - 1; wt += __builtin_popcountll(v); }
    printf("m=%d weight(X)=%ld  2^(m-1)=%ld  diff=%ld  parity=%ld\n", m, wt, N / 2, wt - N / 2, wt & 1);
    for (int s = 0; s < m; s++) { free(A[s]); free(B[s]); free(C[s]); }
    free(A); free(B); free(C);
  }
  return 0;
}
