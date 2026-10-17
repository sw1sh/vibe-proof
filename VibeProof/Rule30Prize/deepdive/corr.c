/* corr.c — agreement of Ψ(∅) (raw 0/1 bytes, depths 1..) with single-seed rule 30 objects.
 * Prints the fraction of agreement and a z-score (0 for independent fair coins).
 *   (a) Ψ(k) vs the centre column c(k + d), shifts d in [-64, 64]
 *   (b) Ψ(k) vs the single-seed left row cell(T, -k), and right row cell(T, k), for several T
 * usage: corr psi_file T_max
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb");
  long T = argc > 2 ? atol(argv[2]) : 8192;
  unsigned char *psi = malloc(T + 2);
  if (fread(psi + 1, 1, T, f) != (size_t)T) return 2;
  fclose(f);
  long off = T + 2, n = 2 * T + 5;
  unsigned char *a = calloc(n, 1), *b = calloc(n, 1), *c = calloc(T + 200, 1);
  unsigned char **rows = calloc(T + 1, sizeof(char *));
  long snap[] = {T / 8, T / 4, T / 2, T, 0};
  a[off] = 1;
  for (long t = 0; t <= T; t++) {
    c[t] = a[off];
    for (int i = 0; snap[i]; i++) if (snap[i] == t) { rows[t] = malloc(n); memcpy(rows[t], a, n); }
    if (t == T) break;
    for (long p = 1; p + 1 < n; p++) b[p] = a[p - 1] ^ (a[p] | a[p + 1]);
    unsigned char *tmp = a; a = b; b = tmp;
  }
  /* (a) centre column with shifts */
  double worst = 0; long wd = 0;
  for (long d = -64; d <= 64; d++) {
    long agree = 0, cnt = 0;
    for (long k = 1; k <= T; k++) { long t = k + d; if (t < 0 || t > T) continue; agree += psi[k] == c[t]; cnt++; }
    double z = (2.0 * agree - cnt) / sqrt((double)cnt);
    if (fabs(z) > fabs(worst)) { worst = z; wd = d; }
  }
  printf("(a) centre column, 129 shifts: largest |z| = %.2f at shift %ld (expect max |z| ~ 3 by chance)\n", worst, wd);
  /* (b) rows */
  for (int i = 0; snap[i]; i++) {
    long t = snap[i]; long agL = 0, agR = 0;
    for (long k = 1; k <= t; k++) { agL += psi[k] == rows[t][off - k]; agR += psi[k] == rows[t][off + k]; }
    printf("(b) T=%6ld  left row agree %.4f (z %.2f)   right row agree %.4f (z %.2f)\n", t,
           (double)agL / t, (2.0 * agL - t) / sqrt((double)t), (double)agR / t, (2.0 * agR - t) / sqrt((double)t));
  }
  return 0;
}
