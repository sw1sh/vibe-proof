/* ucheck.c — is u(R) eventually periodic? u(R)_s = column +1 at time 2s+1 of the right half,
 * driven by the alternating centre (black at even times), started from a finite right half R.
 * T175 (Rule30ZeroBoundary.free_not_eventuallyPeriodic): the free bits of a finite constrained
 * left row are never eventually periodic, so an eventually periodic u(R) settles CQ01 at R.
 *
 * usage: ucheck T Pmax [R bits as a string, e.g. 101 = cells 1..3]
 * Reports the smallest P <= Pmax with u_s = u_{s+P} for every s in [S/2, S - P), S = T/2,
 * and the density of u.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t u64;

int main(int argc, char **argv) {
  long T = argc > 1 ? atol(argv[1]) : 262144;
  long Pmax = argc > 2 ? atol(argv[2]) : 4096;
  const char *Rs = argc > 3 ? argv[3] : "";
  long V = strlen(Rs);
  long nw = (T + V + 4) / 64 + 2;
  u64 *row = calloc(nw, 8), *nx = calloc(nw, 8);
  for (long i = 0; i < V; i++) if (Rs[i] == '1') row[(i + 1) >> 6] |= 1ULL << ((i + 1) & 63);
  long S = T / 2;
  unsigned char *u = malloc(S + 1);
  long ones = 0;
  for (long t = 0; t < T; t++) {
    if ((t & 1) == 0) row[0] |= 1ULL; else row[0] &= ~1ULL;           /* driver */
    if (t & 1) { u[t / 2] = (row[0] >> 1) & 1; ones += u[t / 2]; }   /* column 1 at t = 2s+1 */
    long w = (t + V + 3) / 64 + 2; if (w > nw) w = nw;
    for (long i = 0; i < w; i++) {
      u64 a = row[i];
      u64 left = (a << 1) | (i ? row[i - 1] >> 63 : 0);
      u64 right = (a >> 1) | (i + 1 < nw ? row[i + 1] << 63 : 0);
      nx[i] = left ^ (a | right);
    }
    u64 *tmp = row; row = nx; nx = tmp;
  }
  printf("R=%s  T=%ld  u density %.4f\n", V ? Rs : "(empty)", T, (double)ones / S);
  long best = -1;
  for (long P = 1; P <= Pmax && best < 0; P++) {
    long s; for (s = S / 2; s + P < S; s++) if (u[s] != u[s + P]) break;
    if (s + P >= S) best = P;
  }
  if (best > 0) {
    long s0 = S / 2; while (s0 > 0 && u[s0 - 1] == u[s0 - 1 + best]) s0--;
    printf("eventually periodic: period %ld from s = %ld (time %ld)\n", best, s0, 2 * s0 + 1);
  } else printf("no period <= %ld on the second half of [0, %ld)\n", Pmax, S);
  return 0;
}
