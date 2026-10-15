// Certified termination for the family  x0 = S[1..m] . v . 0^inf   (S = stripe, |v| = L), all m >= 0.
// For each v and each parity of m:
//   d = m + delta (first depth where x0 differs from S); the front window W_t (K cells at depths d-t ..)
//   evolves autonomously (one-way rule, stripe ahead of the front).  The state (W_t, parity of d-t) has an
//   eventually periodic orbit; Brent's algorithm gives preperiod mu and period lambda.  Arrival time t_a = d-1.
//   Every arrival state is W_t for some t < mu + lambda (with the right parity class), so
//   sigma_max = max over those t of the post-arrival survival bounds D(x0) - t_a for ALL m >= m_min.
// Post-arrival survival is computed from the K-cell window (reliable for K-2 steps); if some state survives
// K-2 steps the certificate fails (reported).
// Death time D(x0) = t_a + sigma.  Output: max sigma, max (mu+lambda).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int K;
static uint64_t MASK;
static inline uint64_t fstep(uint64_t W, int fodd){
  // window bits i <-> depths f+i; stripe ahead: S(f-1) = (f-1)&1, S(f-2) = f&1
  uint64_t s1 = fodd ? 0 : 1, s2 = fodd ? 1 : 0;
  return (W ^ (((W << 1) | s1) | ((W << 2) | (s1 << 1) | s2))) & MASK;
}
static int sigma_of(uint64_t W, long ta){
  uint64_t x = W;
  for (int s = 0; s < K - 2; s++){
    long time = ta + s;
    if (!(time & 1) && !(x & 1)) return s;
    x = ((x >> 1) ^ (x | (x << 1))) & MASK;
  }
  return -1;
}
int main(int argc, char **argv){
  int L = atoi(argv[1]); K = atoi(argv[2]);
  int vlo = argc > 3 ? atoi(argv[3]) : 0, vhi = argc > 4 ? atoi(argv[4]) : (1 << L);
  MASK = (K == 64) ? ~0ULL : ((1ULL << K) - 1);
  int smax = -1; long orbmax = 0; long fails = 0; int worst_v = -1, worst_par = -1; long worst_t = -1;
  for (int vb = vlo; vb < vhi; vb++){
    for (int mpar = 0; mpar < 2; mpar++){
      // representative m with parity mpar; x0 bits at depths m+1..m+L = v; S(k) = k&1
      long m = 1000 + mpar;
      long d = -1;
      for (long k = m + 1; k <= m + L + 2; k++){
        int xv = (k <= m + L) ? ((vb >> (k - m - 1)) & 1) : 0;
        if (xv != (int)(k & 1)) { d = k; break; }
      }
      long delta = d - m;
      uint64_t W0 = 0;
      for (int i = 0; i < K; i++){
        long k = d + i;
        int xv = (k <= m + L) ? ((vb >> (k - m - 1)) & 1) : 0;
        if (xv) W0 |= 1ULL << i;
      }
      // state: (W, parity of f_t) ; f_t = d - t; parity of f_t = (d - t) & 1
      // Brent's cycle detection on t -> state; parity of f flips each step, so encode state as (W, (d-t)&1)
      int p0 = (int)(d & 1);
      // power/lambda
      long power = 1, lam = 1;
      uint64_t tortW = W0; int tortP = p0;
      uint64_t hareW = fstep(W0, p0); int hareP = p0 ^ 1;
      while (!(tortW == hareW && tortP == hareP)){
        if (power == lam){ tortW = hareW; tortP = hareP; power <<= 1; lam = 0; }
        hareW = fstep(hareW, hareP); hareP ^= 1; lam++;
        if (power > (1L << 40)) { printf("cycle too long\n"); return 1; }
      }
      // find mu
      tortW = W0; tortP = p0; hareW = W0; hareP = p0;
      for (long i = 0; i < lam; i++){ hareW = fstep(hareW, hareP); hareP ^= 1; }
      long mu = 0;
      while (!(tortW == hareW && tortP == hareP)){
        tortW = fstep(tortW, tortP); tortP ^= 1; hareW = fstep(hareW, hareP); hareP ^= 1; mu++;
      }
      if (mu + lam > orbmax) orbmax = mu + lam;
      // scan t in [0, mu+lam): arrival times t_a = m + delta - 1 have parity (mpar + delta - 1) & 1
      uint64_t W = W0; int P = p0;
      int want = (int)((mpar + delta - 1) & 1);
      for (long t = 0; t < mu + lam; t++){
        if ((t & 1) == want){
          int s = sigma_of(W, t);
          if (s < 0) { fails++; if (fails <= 3) printf("FAIL v=%d mpar=%d t=%ld\n", vb, mpar, t); }
          else if (s > smax) { smax = s; worst_v = vb; worst_par = mpar; worst_t = t; }
        }
        W = fstep(W, P); P ^= 1;
      }
    }
  }
  printf("L=%d K=%d v in [%d,%d): max sigma = %d (v=%d, m parity %d, at t=%ld), max orbit (mu+lambda) = %ld, fails = %ld\n",
         L, K, vlo, vhi, smax, worst_v, worst_par, worst_t, orbmax, fails);
  return 0;
}
