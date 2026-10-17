/* psi.c — the left row Ψ(∅) of the coupled period-2 problem with an empty right half.
 *
 * Setting (rule 30: new(p) = old(p-1) XOR (old(p) OR old(p+1))):
 *   centre column c(t) = 1 for even t, 0 for odd t (the alternation, black at t = 0);
 *   right half (p >= 1) white at time 0, then driven by the centre;
 *   left half: column -1 is forced by the alternation, and every deeper column follows
 *   sideways by left-permutivity:  X_{k+1}(t) = X_k(t+1) XOR (X_k(t) OR X_{k-1}(t)),
 *   with X_{-1} = column +1, X_0 = centre, X_k = column -k.
 * Ψ(∅)(k) = X_k(0): the only time-0 left row that keeps the centre alternating forever.
 * CQ01 at R = ∅  <=>  Ψ(∅) has infinitely many 1s.
 *
 * usage: psi K [outfile]     computes Ψ(∅)(1..K), prints statistics, optionally writes the
 *                            bits (one raw byte per depth, 0 or 1) to outfile.
 *        psi K - W1 W2 ...    also brute-force checks the exact-death identity for the
 *                            truncations of Ψ(∅) to widths W1, W2, ...
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;

static void shr1(u64 *dst, const u64 *src, long nw) { /* dst bit t = src bit t+1 */
  for (long i = 0; i < nw; i++) dst[i] = (src[i] >> 1) | (i + 1 < nw ? src[i + 1] << 63 : 0);
}
static void shl1(u64 *dst, const u64 *src, long nw) { /* dst bit p = src bit p-1 */
  for (long i = nw - 1; i >= 0; i--) dst[i] = (src[i] << 1) | (i > 0 ? src[i - 1] >> 63 : 0);
}
static int getb(const u64 *a, long i) { return (a[i >> 6] >> (i & 63)) & 1; }
static void setb(u64 *a, long i, int v) {
  if (v) a[i >> 6] |= 1ULL << (i & 63); else a[i >> 6] &= ~(1ULL << (i & 63));
}

/* brute force: finite configuration L (depths 1..W) | centre 1 | right empty; returns the
   first time t >= 1 at which the centre is not (t even ? 1 : 0), or -1 if none up to T. */
static long brute_death(const unsigned char *psi, long W, long T) {
  long off = W + T + 2, n = off + T + 3;
  unsigned char *a = calloc(n, 1), *b = calloc(n, 1);
  for (long k = 1; k <= W; k++) a[off - k] = psi[k];
  a[off] = 1;
  for (long t = 0; t < T; t++) {
    for (long p = 1; p + 1 < n; p++) b[p] = a[p - 1] ^ (a[p] | a[p + 1]);
    b[0] = 0; b[n - 1] = 0;
    unsigned char *tmp = a; a = b; b = tmp;
    if (a[off] != (((t + 1) & 1) == 0)) { free(a); free(b); return t + 1; }
  }
  free(a); free(b);
  return -1;
}

int main(int argc, char **argv) {
  long K = argc > 1 ? atol(argv[1]) : 65536;
  long nw = (K + 2) / 64 + 2;
  u64 *row = calloc(nw, 8), *tmp = calloc(nw, 8), *tmp2 = calloc(nw, 8);
  u64 *col1 = calloc(nw, 8), *cen = calloc(nw, 8);
  /* right half driven by the alternating centre; row bit p = cell (t, p), p = 0..K+1 */
  for (long t = 0; t <= K; t++) {
    setb(row, 0, (t & 1) == 0);
    setb(cen, t, (t & 1) == 0);
    setb(col1, t, getb(row, 1));
    shl1(tmp, row, nw);            /* left neighbour  */
    shr1(tmp2, row, nw);           /* right neighbour */
    for (long i = 0; i < nw; i++) row[i] = tmp[i] ^ (row[i] | tmp2[i]);
  }
  /* sideways recurrence over depth */
  unsigned char *psi = calloc(K + 2, 1);
  u64 *Xm = col1, *X0 = cen, *X1 = calloc(nw, 8);
  for (long k = 0; k < K; k++) {
    long valid = K - k;            /* X_k is valid for t <= K - k */
    long w = valid / 64 + 1;
    shr1(X1, X0, w);
    for (long i = 0; i < w; i++) X1[i] ^= (X0[i] | Xm[i]);
    psi[k + 1] = getb(X1, 0);
    u64 *old = Xm; Xm = X0; X0 = X1; X1 = old;
  }
  /* statistics */
  long ones = 0, run = 0, maxrun = 0, nextpow = 2;
  printf("depth  ones/depth  longest_zero_run_so_far\n");
  for (long k = 1; k <= K; k++) {
    ones += psi[k];
    run = psi[k] ? 0 : run + 1;
    if (run > maxrun) maxrun = run;
    if (k == nextpow) { printf("%7ld  %.4f  %ld\n", k, (double)ones / k, maxrun); nextpow *= 2; }
  }
  printf("first 64: ");
  for (long k = 1; k <= 64 && k <= K; k++) putchar('0' + psi[k]);
  printf("\n");
  if (argc > 2 && strcmp(argv[2], "-") != 0) {
    FILE *f = fopen(argv[2], "w");
    fwrite(psi + 1, 1, K, f);
    fclose(f);
    for (long k = 1; k <= K; k++) {}
  }
  /* exact-death checks: truncate Ψ(∅) to width W; predicted death = first black depth > W */
  for (int i = 3; i < argc; i++) {
    long W = atol(argv[i]);
    long a = W + 1; while (a <= K && !psi[a]) a++;
    long d = brute_death(psi, W, 3 * W + 64);
    printf("W=%ld  first black depth beyond W: %ld   brute-force death time: %ld\n", W, a, d);
  }
  return 0;
}
