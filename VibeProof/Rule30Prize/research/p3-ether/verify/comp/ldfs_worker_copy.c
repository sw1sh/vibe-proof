// Exhaustive death-time search for constrained driven left halves (period-3 analogs of Q01).
// Left half: depth i >= 1 (position -i), boundary column x_0(t) = c'(t) (periodic word E, phase offset ph0).
// Constraint on column -1: x_1(t) must equal K[(ph0 + t) % P] where K[] is '0', '1' or '*' (free).
// Anti-diagonals A_m(t) = x_{m-t}(t), 0 <= t <= m:  A_m(m) = c'(m),  A_{m+1}(m) = x_1(m),
//   A_{m+1}(t) = A_{m+1}(t+1) xor (A_m(t) or A_{m-1}(t))  (t < m).
// Initial row L(k) = x_k(0) = A_k(0); support width <= W means L(k) = 0 for k > W.
// For each W, enumerates every start of width <= W (via the column -1 history) and reports the largest
// number of steps a constrained history survives (max over starts of the first violation time),
// and how many starts of width exactly W survive to each time.
// usage: ldfs E K ph0 W0 W1 [maxdepth]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NW 4
typedef struct { uint64_t w[NW]; } bv;
static const char *E, *K; static int P, ph0, W, MAXD;
static long long surv[NW * 64 + 2]; static int deepest; static long long nodes;
static inline int getb(const bv *a, int i) { return (int)((a->w[i >> 6] >> (i & 63)) & 1); }
static inline void setb(bv *a, int i, int v) { if (v) a->w[i >> 6] |= 1ULL << (i & 63); else a->w[i >> 6] &= ~(1ULL << (i & 63)); }
static inline uint64_t sxor64(uint64_t s) { s ^= s >> 1; s ^= s >> 2; s ^= s >> 4; s ^= s >> 8; s ^= s >> 16; s ^= s >> 32; return s; }
// build A_{m+1} from A_{m-1}, A_m and x = x_1(m):  bits t < m: x xor XOR_{s=t}^{m-1} (A_m(s) | A_{m-1}(s)); bit m = x; bit m+1 = c'(m+1)
static inline void build(const bv *Am1, const bv *Am, int m, int x, int cnext, bv *out) {
    uint64_t g[NW];
    for (int i = 0; i < NW; i++) {
        uint64_t v = Am->w[i] | Am1->w[i]; int lo = 64 * i;
        if (m <= lo) v = 0; else if (m < lo + 64) v &= (1ULL << (m - lo)) - 1;
        g[i] = v;
    }
    int carry = 0;
    for (int i = NW - 1; i >= 0; i--) {
        uint64_t s = sxor64(g[i]); if (carry) s = ~s; carry ^= __builtin_parityll(g[i]);
        int lo = 64 * i; uint64_t mk; if (m <= lo) mk = 0; else if (m >= lo + 64) mk = ~0ULL; else mk = (1ULL << (m - lo)) - 1;
        s &= mk; if (x) s ^= mk; out->w[i] = s;
    }
    setb(out, m, x); if (m + 1 < NW * 64) setb(out, m + 1, cnext);
}
static void dfs(int m, const bv *Am1, const bv *Am) {
    // x_1(0..m-1) chosen consistently; the history survives through time m-1
    surv[m]++; if (m > deepest) deepest = m;
    if (m >= MAXD) { printf("MAXD reached at W=%d: inconclusive\n", W); exit(2); }
    int ph = (ph0 + m) % P; char k = K[ph];
    for (int x = 0; x <= 1; x++) {
        if (k != '*' && x != k - '0') continue;
        bv An; build(Am1, Am, m, x, E[(ph0 + m + 1) % P] - '0', &An); nodes++;
        if (m + 1 > W && getb(&An, 0)) continue;   // L(m+1) must be 0
        dfs(m + 1, Am, &An);
    }
}
int main(int argc, char **argv) {
    E = argv[1]; K = argv[2]; P = (int)strlen(E); ph0 = atoi(argv[3]); int W0 = atoi(argv[4]), W1 = atoi(argv[5]);
    MAXD = argc > 6 ? atoi(argv[6]) : NW * 64 - 4;
    if ((int)strlen(K) != P) { fprintf(stderr, "E and K must have equal length\n"); return 1; }
    for (W = W0; W <= W1; W++) {
        memset(surv, 0, sizeof surv); deepest = 0; nodes = 0;
        bv Am1, A0; memset(&Am1, 0, sizeof Am1); memset(&A0, 0, sizeof A0);
        setb(&A0, 0, E[ph0 % P] - '0');           // A_0 = (x_0(0)) = c'(0)
        dfs(0, &Am1, &A0);
        // deepest = largest m with a consistent prefix x_1(0..m-1): every start of width <= W violates the
        // constraint at some time < deepest + 1 (i.e. by time deepest)
        printf("E=%s K=%s ph0=%d W=%2d: max survival %3d steps (all starts of width <= W violate by time %d); nodes %lld\n",
               E, K, ph0, W, deepest, deepest, nodes);
        fflush(stdout);
    }
    return 0;
}
