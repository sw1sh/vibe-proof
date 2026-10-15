/* Local front lemma: cells m, m+1, ... follow the stripe (m odd: cell m = 1, m+1 = 0, ...).
   Window cells m-w .. m-1 arbitrary (w = tau+2); cells below m-w arbitrary/unknown.
   Within tau steps, (cell m-2, cell m-1) = (1, 0) must occur.  Cells m-2, m-1 at time s <= tau depend
   only on cells >= m-2-s >= m-w at time 0, so filling the unknown cells with 0 is exact for them.
   We work with a register: bit i <-> cell m-w+i (i = 0..w-1), plus stripe cells m (=1), m+1 (=0).
   Usage: frontlemma tau     prints the number of window configurations that FAIL. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int tau = atoi(argv[1]); int w = tau + 2;
  uint64_t N = 1ULL << w; long fails = 0; int worst = 0;
  for (uint64_t c = 0; c < N; c++) {
    /* ext bit j <-> cell m-w-1+j : j=0 is the unknown cell below the window (0), j=1..w window, j=w+1 cell m (1), j = w+2 cell m+1 (0) */
    uint64_t v = c;   /* bit i <-> cell m-w+i */
    int ok = 0, s;
    for (s = 0; s <= tau; s++) {
      int cm2 = (v >> (w - 2)) & 1, cm1 = (v >> (w - 1)) & 1;
      if (cm2 == 1 && cm1 == 0) { ok = 1; break; }
      uint64_t ext = (v << 1) | (1ULL << (w + 1));     /* bit 0 = unknown cell below (0), cell m = 1, cell m+1 = 0 */
      uint64_t nw = (ext >> 1) ^ (ext | (ext << 1));   /* new(j) = ext[j+1] ^ (ext[j] | ext[j-1]) */
      v = (nw >> 1) & (N - 1);
    }
    if (!ok) fails++; else if (s > worst) worst = s;
  }
  printf("tau=%d (window %d cells): failing configurations %ld, worst event time among successes %d\n", tau, w, fails, worst);
  return 0;
}
