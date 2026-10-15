// Exhaustive maximal survival time for the period-2 constraint on the zero-boundary left half (ZBL).
// Column -1: y_t = x_t(-1).  Constraint: y_t = 1 for all even t.  Free bits f_s = y_{2s+1}.
// Anti-diagonals D_k(j) = x_j(-(k-j)), j = 0..k-1.  Recursion: D_{k+1}(0) = x_{k+1} (initial cell at depth k+1),
// D_{k+1}(j) = D_{k+1}(j-1) xor (D_k(j-1) or D_{k-1}(j-1)), and y_k = D_{k+1}(k).
// For a configuration of width <= W: x_{k+1} = 0 for k+1 > W.
// Modes: 0 = plain Q_01; 1 = golden mean on f (no f_s = f_{s+1} = 0); 2 = golden mean and no 11111 in f.
// Output: for each W, max death time, number of leaves with that max, survivors by depth.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NWD 4
typedef struct { uint64_t w[NWD]; } BV;
static int W, MODE, MAXK;
static long long best_cnt; static int best;
static long long surv[300];
static inline int getbit(const BV *v, int i) { return (v->w[i >> 6] >> (i & 63)) & 1; }
// prefix xor inclusive over bits 0..n-1, returns vector P with P(j) = v(0)^...^v(j)
static inline void pxor(const BV *v, BV *P) {
    uint64_t carry = 0;
    for (int q = 0; q < NWD; q++) {
        uint64_t x = v->w[q];
        x ^= x << 1; x ^= x << 2; x ^= x << 4; x ^= x << 8; x ^= x << 16; x ^= x << 32;
        if (carry) x = ~x;
        P->w[q] = x;
        carry = (x >> 63) & 1;
    }
}
static inline void mask_to(BV *v, int n) { // keep bits 0..n-1
    for (int q = 0; q < NWD; q++) {
        int lo = q * 64;
        if (n <= lo) v->w[q] = 0;
        else if (n < lo + 64) v->w[q] &= (n - lo == 64) ? ~0ULL : ((1ULL << (n - lo)) - 1);
    }
}
// f history for constraints: last free bits
static void dfs(const BV *Dkm1, const BV *Dk, int k, int fprev, int run1) {
    // Dk has k entries (bits 0..k-1); choose y_k, compute D_{k+1}
    surv[k]++;
    if (k >= MAXK) { if (k > best) { best = k; best_cnt = 0; } best_cnt++; return; }
    BV v, P, Dn;
    for (int q = 0; q < NWD; q++) v.w[q] = Dk->w[q] | Dkm1->w[q];
    mask_to(&v, k);
    pxor(&v, &P);
    // S(j) = P(j-1) for j>=1, S(0)=0  -> Sv = P << 1
    BV Sv; uint64_t c = 0;
    for (int q = 0; q < NWD; q++) { uint64_t x = P.w[q]; Sv.w[q] = (x << 1) | c; c = x >> 63; }
    int Sk = getbit(&Sv, k);       // S(k) = parity of v
    int even = (k % 2 == 0);
    for (int yk = 0; yk <= 1; yk++) {
        if (even && yk != 1) continue;
        int xk1 = yk ^ Sk;            // initial cell at depth k+1
        if (k + 1 > W && xk1 != 0) continue;
        int nf = fprev, nr = run1;
        if (!even) {
            int fs = yk;
            if (MODE >= 1 && fprev == 0 && fs == 0) continue;
            nr = fs ? run1 + 1 : 0;
            if (MODE >= 2 && nr >= 5) continue;
            nf = fs;
        }
        for (int q = 0; q < NWD; q++) Dn.w[q] = Sv.w[q] ^ (xk1 ? ~0ULL : 0);
        mask_to(&Dn, k + 1);
        dfs(Dk, &Dn, k + 1, nf, nr);
    }
    // death: if even and the check fails (only possible branch yk=1 rejected because k+1>W and xk1 != 0)
    if (even && k + 1 > W && (1 ^ Sk) != 0) {
        if (k > best) { best = k; best_cnt = 0; }
        if (k == best) best_cnt++;
    }
}
int main(int argc, char **argv) {
    int W0 = atoi(argv[1]), W1 = atoi(argv[2]); MODE = argc > 3 ? atoi(argv[3]) : 0;
    MAXK = 250;
    for (W = W0; W <= W1; W++) {
        BV z; memset(&z, 0, sizeof z);
        memset(surv, 0, sizeof surv);
        best = -1; best_cnt = 0;
        dfs(&z, &z, 0, 1, 0);
        printf("mode=%d W=%d maxdeath=%d (#=%lld) ratio=%.3f  survivors@W=%lld", MODE, W, best, best_cnt, best / (double)(W ? W : 1), surv[W]);
        printf("  tail:");
        for (int k = W; k <= best + 1 && k < 300; k += 2) printf(" %lld", surv[k]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
