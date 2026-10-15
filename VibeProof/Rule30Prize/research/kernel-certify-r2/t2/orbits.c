/* Front-window orbits for x = S[1..m] . v . 0^inf, v in {0,1}^3 (bit i of vb = v[i], depth m+1+i).
   Window W_t: bits i <-> depth d - t + i, K bits; state (W, (d - t) % 2).
   Post-arrival check (exact light cone): s <= S with S + 1 <= K, unmasked ZBL steps on the window.
   Prints per class: q = m%2, vb, delta, W0, mu, lambda, max sigma over r < mu+lambda with r%2 == (d-1)%2. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int K; static uint64_t MASK;
static uint64_t fstep(uint64_t W, int fodd){ uint64_t s1 = fodd ? 0 : 1, s2 = fodd ? 1 : 0;
  return (W ^ (((W << 1) | s1) | ((W << 2) | (s1 << 1) | s2))) & MASK; }
static int sigma(uint64_t W, long r, int S){ u128 x = W;
  for (int s = 0; s <= S; s++){ if (((r + s) % 2 == 0) && !(x & 1)) return s; x = (x >> 1) ^ (x | (x << 1)); }
  return -1; }
int main(int argc, char **argv){
  K = atoi(argv[1]); int S = atoi(argv[2]); MASK = (K == 64) ? ~0ULL : ((1ULL << K) - 1);
  for (int q = 0; q < 2; q++) for (int vb = 0; vb < 8; vb++){
    long m = 1000 + q; long d = -1;
    for (long k = m + 1; k <= m + 5; k++){ int xv = (k <= m + 3) ? ((vb >> (k - m - 1)) & 1) : 0; if (xv != (int)(k & 1)) { d = k; break; } }
    uint64_t W0 = 0; for (int i = 0; i < K; i++){ long k = d + i; int xv = (k <= m + 3) ? ((vb >> (k - m - 1)) & 1) : 0; if (xv) W0 |= 1ULL << i; }
    int p0 = (int)(d & 1);
    /* Brent */
    long power = 1, lam = 1; uint64_t tW = W0; int tP = p0; uint64_t hW = fstep(W0, p0); int hP = p0 ^ 1;
    while (!(tW == hW && tP == hP)){ if (power == lam){ tW = hW; tP = hP; power <<= 1; lam = 0; } hW = fstep(hW, hP); hP ^= 1; lam++; }
    tW = W0; tP = p0; hW = W0; hP = p0; for (long i = 0; i < lam; i++){ hW = fstep(hW, hP); hP ^= 1; }
    long mu = 0; while (!(tW == hW && tP == hP)){ tW = fstep(tW, tP); tP ^= 1; hW = fstep(hW, hP); hP ^= 1; mu++; }
    int want = (int)((d - 1) & 1); int smax = -1; long fails = 0; uint64_t W = W0; int P = p0;
    for (long t = 0; t < mu + lam; t++){ if ((t & 1) == want){ int s = sigma(W, t, S); if (s < 0) fails++; else if (s > smax) smax = s; } W = fstep(W, P); P ^= 1; }
    printf("q=%d vb=%d delta=%ld W0=%llu mu=%ld lam=%ld maxsigma=%d fails=%ld\n", q, vb, d - m, (unsigned long long)W0, mu, lam, smax, fails);
  }
  return 0;
}
