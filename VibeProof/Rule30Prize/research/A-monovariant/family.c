// T5: configurations stripe^n . u . 0^inf (x_k = [k odd] for k<=n, x_{n+i} = u_i, then zeros), phase 0.
// For each u and each parity of n: first defect e = n + c (c = offset in u of first mismatch with the stripe continuation).
// If e is odd -> violation at time e-1 (even).  If e even -> at time e-1 (odd) the config is x_{1+j}(e-1) = Y_j(e-1), where
// Y_j(t) = x_{e-t+j}(t) obeys Y_j(t+1) = Y_j(t) ^ (Y_{j-1}(t) | Y_{j-2}(t)) with Y_0(t) = !s(e-t), Y_{-1}(t) = s(e-t-1),
// Y_{-2}(t) = s(e-t-2); this map on (Y_1..Y_J, t mod 2) is a bijection, so the state sequence is purely periodic.
// For every state in the orbit with t odd (reset time, e-1 odd), run the ZBL on the first J+1 cells and require a violation
// within J steps (only cells 1..J+1-i are trusted after i steps).  If all states pass, stripe^n.u dies for EVERY n of that parity,
// at time <= e-1+J.  We increase J until this works (or give up).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define JMAX 120
static int s(long k) { return (int)(((k % 2) + 2) % 2); }   // stripe: 1 at odd k (k>=0); s(0)=0
// returns death offset (>=0) after time e-1, or -1 if not determined within J steps
static int zbl_check(const unsigned char *cfg, int J) {
  // cfg[1..J+1] = x_1..x_{J+1} at time e-1 (odd).  Time e-1+i; violation if x_1 = 0 at even time, i.e. i odd.
  unsigned char a[JMAX + 4], b[JMAX + 4];
  memcpy(a, cfg, J + 2); a[0] = 0;
  int valid = J + 1;
  for (int i = 0; i <= J; i++) {
    if (valid < 1) return -1;
    if ((i & 1) && !a[1]) return i;
    // step
    for (int k = 1; k < valid; k++) b[k] = a[k + 1] ^ (a[k] | a[k - 1]);
    b[0] = 0; valid--;
    memcpy(a, b, valid + 1);
  }
  return -1;
}
// orbit check. Y[0..J] ; returns max death offset over orbit states with t odd, or -1 if some state undetermined; *period out
static int check_family(const unsigned char *Y0, int J, long e_parity, long *period, long maxper) {
  unsigned char Y[JMAX + 4], start[JMAX + 4];
  memcpy(Y, Y0, J + 1);
  memcpy(start, Y, J + 1);
  int worst = 0;
  long t = 0;
  // e - t parity: s(e - t) where e has parity e_parity
  while (1) {
    // state at time t: Y_0(t) = !s(e - t)
    int par_et = (int)((e_parity - t) % 2 + 2) % 2;      // parity of e - t
    Y[0] = !(par_et == 1);
    if (t & 1) {
      unsigned char cfg[JMAX + 4];
      cfg[0] = 0;
      for (int j = 0; j <= J; j++) cfg[j + 1] = Y[j];
      int d = zbl_check(cfg, J);
      if (d < 0) return -1;
      if (d > worst) worst = d;
    }
    // advance: Y_j(t+1) = Y_j(t) ^ (Y_{j-1}(t) | Y_{j-2}(t)); Y_{-1}(t) = s(e-t-1), Y_{-2}(t) = s(e-t-2)
    int ym1 = ((par_et + 1) % 2 == 0) ? 1 : 0;   // s(e-t-1): parity of e-t-1 odd -> 1
    ym1 = ((par_et + 1) & 1) ? 0 : 1;
    // careful: s(k) = 1 iff k odd. e-t-1 odd iff par_et even.
    ym1 = (par_et == 0) ? 1 : 0;
    unsigned char N[JMAX + 4];
    for (int j = 1; j <= J; j++) {
      int a1 = Y[j - 1];
      int a2 = (j >= 2) ? Y[j - 2] : ym1;
      N[j] = Y[j] ^ (a1 | a2);
    }
    for (int j = 1; j <= J; j++) Y[j] = N[j];
    t++;
    if (t % 2 == 0 && memcmp(Y + 1, start + 1, J) == 0) { *period = t; break; }
    if (t > maxper) return -2;
  }
  return worst;
}
int main(int argc, char **argv) {
  int R0 = atoi(argv[1]);
  long maxper = argc > 2 ? atol(argv[2]) : (1L << 24);
  int globalJ = 0; long globalper = 0; int fails = 0; long count = 0;
  for (int r = 1; r <= R0; r++) {
    for (uint32_t u = 0; u < (1u << r); u++) {
      if (!((u >> (r - 1)) & 1)) continue;        // last bit of u is 1 (exact tail)
      for (int np = 0; np <= 1; np++) {
        // position n+i has stripe value s(n+i); parity np of n
        int c = -1;
        for (int i = 1; i <= r; i++) { int si = s(np + i); if ((int)((u >> (i - 1)) & 1) != si) { c = i; break; } }
        if (c < 0) {
          // u agrees with stripe continuation; first defect is after u: positions n+r+1.. are 0; s(n+r+1)?
          int i = r + 1; while (s(np + i) == 0) i++; c = i;   // first odd position (stripe 1) where we have 0
        }
        long e_par = (np + c) % 2;
        count++;
        if (e_par == 1) continue;           // e odd: violation at time e-1 (even) for every such n
        // Y_j(0) = x_{e+j}(0) = u_{c+j} (j >= 0), zeros beyond r
        int J, ok = 0; long per = 0; int worst = 0;
        for (J = 4; J <= JMAX - 2; J += 4) {
          unsigned char Y0[JMAX + 4];
          for (int j = 0; j <= J; j++) { int i = c + j; Y0[j] = (i <= r) ? ((u >> (i - 1)) & 1) : 0; }
          // check Y0[0] = !s(e) = !s(c+np) consistent
          worst = check_family(Y0, J, e_par, &per, maxper);
          if (worst >= 0) { ok = 1; break; }
          if (worst == -2) break;
        }
        if (!ok) { fails++; printf("FAIL u="); for (int i = 0; i < r; i++) putchar((u >> i) & 1 ? '1' : '0'); printf(" n-parity=%d (J up to %d, code %d)\n", np, J, worst); continue; }
        if (J > globalJ) globalJ = J;
        if (per > globalper) globalper = per;
      }
    }
    printf("r<=%d: families checked %ld, failures %d, max J needed %d, max orbit period %ld\n", r, count, fails, globalJ, globalper);
    fflush(stdout);
  }
}
