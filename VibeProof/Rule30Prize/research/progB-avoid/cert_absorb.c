// Certified absorption of w-driven finite right halves.
// For a configuration (columns 1..), simulate; at checkpoints, take the width-B strip state (B in a list),
// compute its forward closure under ALL inputs at column B+1 (BFS, size limit), and check that the closure is
// consistently labelled by the periodic word of the true future output (column 1 at white phases).
// If so, the output is periodic from that time on (the true path stays in the closure) -- certified absorption.
// usage: cert_absorb w mode n trials maxT seed
//   mode 0: random configs with support exactly [1,n], random phase; mode 2: exhaustive support within [1,n], all phases
//   mode 1: true rule-30 right half at time T=n, phases 0..P-1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int P; static const char *W;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
#define MAXW 512
static void step(uint64_t *a, int nw, int cphi) {
    uint64_t prevtop = (uint64_t)cphi;
    for (int k = 0; k < nw; k++) {
        uint64_t cur = a[k];
        uint64_t left = (cur << 1) | prevtop;
        uint64_t right = (cur >> 1) | (k + 1 < nw ? (a[k + 1] << 63) : 0);
        prevtop = cur >> 63;
        a[k] = left ^ (cur | right);
    }
}
// strip transition at width b (b <= 63): returns number of successors
static int succ2(int b, int phi, uint64_t s, uint64_t out[2]) {
    int c = W[phi] - '0';
    uint64_t full = (s << 1) | (uint64_t)c;            // bit p = column p (p=0..b)
    uint64_t left = full;                               // column p-1 at bit p  -> (full) shifted: for column p (bit p of full), left neighbour bit p-1
    // compute new columns 1..b-1: new_p = col_{p-1} ^ (col_p | col_{p+1})
    uint64_t colp = full >> 1;        // bit p-1 = column p
    uint64_t colpm1 = full;           // bit p-1 = column p-1
    uint64_t colpp1 = full >> 2;      // bit p-1 = column p+1 (column b+1 -> 0 here, handled below)
    (void)left;
    uint64_t mask = (b >= 64) ? ~0ULL : ((1ULL << b) - 1);
    uint64_t base = (colpm1 ^ (colp | colpp1)) & mask;  // bit b-1 (column b) computed with column b+1 = 0
    int colb = (int)((s >> (b - 1)) & 1);
    if (colb) { out[0] = base; return 1; }              // column b = 1: input irrelevant (col_b | x = 1) -- base used col_{b+1}=0 but col_b=1 so same
    out[0] = base;                                      // x = 0
    out[1] = base ^ (1ULL << (b - 1));                  // x = 1 flips column b (col_b = 0, so new = col_{b-1} ^ x)
    return 2;
}
// hash set for closure
static uint64_t *hkeys; static int32_t *hpos; static uint64_t hcap;
static inline uint64_t hmix(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return k; }
static int64_t hfind(uint64_t key) { uint64_t h = hmix(key) & (hcap - 1); while (hkeys[h] != UINT64_MAX) { if (hkeys[h] == key) return (int64_t)h; h = (h + 1) & (hcap - 1); } return -(int64_t)h - 1; }
static uint64_t *queue;
// returns closure size if consistent, 0 if inconsistent, -1 if too large
static long closure_consistent(int b, int phi0, uint64_t s0, const int *word, int m, long limit) {
    // key = phase in top bits
    static int inited = 0; static uint64_t *used = NULL; static long nused = 0;
    if (!inited) { for (uint64_t i = 0; i < hcap; i++) hkeys[i] = UINT64_MAX; used = malloc(sizeof(uint64_t) * (limit + 8)); inited = 1; }
    else { for (long i = 0; i < nused; i++) hkeys[used[i]] = UINT64_MAX; }
    nused = 0;
    long qh = 0, qt = 0;
    uint64_t k0 = ((uint64_t)phi0 << 60) | s0;
    int64_t f = hfind(k0); uint64_t slot = (uint64_t)(-f - 1); hkeys[slot] = k0; hpos[slot] = 0; queue[qt++] = k0; used[nused++] = slot;
    while (qh < qt) {
        uint64_t key = queue[qh++]; int phi = (int)(key >> 60); uint64_t s = key & ((1ULL << 60) - 1);
        int64_t fs = hfind(key); int pos = hpos[fs];
        int np;
        if (W[phi] == '0') { if ((int)(s & 1) != word[pos % m]) return 0; np = (pos + 1) % m; } else np = pos;
        uint64_t nb[2]; int nn = succ2(b, phi, s, nb); int nphi = (phi + 1) % P;
        for (int i = 0; i < nn; i++) {
            uint64_t k2 = ((uint64_t)nphi << 60) | nb[i];
            int64_t g = hfind(k2);
            if (g >= 0) { if (hpos[g] != np) return 0; }
            else { if (qt >= limit) return -1; uint64_t sl = (uint64_t)(-g - 1); hkeys[sl] = k2; hpos[sl] = np; queue[qt++] = k2; used[nused++] = sl; }
        }
    }
    return qt;
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W);
    int mode = atoi(argv[2]); int n = atoi(argv[3]); long trials = atol(argv[4]); int maxT = atoi(argv[5]);
    rng ^= (uint64_t)atol(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    int verbose = argc > 7 ? atoi(argv[7]) : 0;
    long limit = 6000; hcap = 1 << 16; while (hcap < 4 * (uint64_t)limit) hcap <<= 1;
    hkeys = malloc(sizeof(uint64_t) * hcap); hpos = malloc(sizeof(int32_t) * hcap); queue = malloc(sizeof(uint64_t) * (limit + 4));
    int widths[] = {16, 20, 24, 28, 32, 40, 48, 56};
    int nwid = sizeof(widths) / sizeof(widths[0]);
    long ncases = mode == 2 ? ((long)1 << n) * P : (mode == 1 ? P : trials);
    long c_lo = argc > 8 ? atol(argv[8]) : 0, c_hi = argc > 9 ? atol(argv[9]) : ncases;
    static uint64_t a[MAXW];
    static uint64_t snap[8192][2]; // strip snapshots (first 64 columns) and phases
    long cnt_abs = 0, cnt_un = 0; long wh[64] = {0}; long maxabs = 0; long tabs_hist[32] = {0};
    int horizon = 400; // future steps needed to read the output word
    for (long tr = c_lo; tr < ncases && tr < c_hi; tr++) {
        memset(a, 0, sizeof(a)); int phase;
        char cfg[1024];
        if (mode == 0) { for (int p = 1; p <= n; p++) { int bit = (p == n || (xr() & 1)); if (bit) a[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63); cfg[p - 1] = '0' + bit; } cfg[n] = 0; phase = xr() % P; }
        else if (mode == 2) { long c = tr / P; phase = tr % P; for (int p = 1; p <= n; p++) { int bit = (c >> (p - 1)) & 1; if (bit) a[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63); cfg[p - 1] = '0' + bit; } cfg[n] = 0; }
        else {
            static uint64_t row[2 * MAXW + 4], nr[2 * MAXW + 4]; int RW = (2 * n + 1 + 63) / 64 + 1; memset(row, 0, sizeof(row));
            row[n >> 6] |= 1ULL << (n & 63);
            for (int t = 0; t < n; t++) { for (int k = 0; k < RW; k++) { uint64_t cur = row[k]; uint64_t l = (cur << 1) | (k ? row[k - 1] >> 63 : 0); uint64_t r = (cur >> 1) | (k + 1 < RW ? row[k + 1] << 63 : 0); nr[k] = l ^ (cur | r); } memcpy(row, nr, sizeof(uint64_t) * RW); }
            for (int p = 1; p <= n; p++) { int i = p + n; if ((row[i >> 6] >> (i & 63)) & 1) a[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63); }
            phase = (int)tr; cfg[0] = 0;
        }
        int ph0 = phase;
        int total = maxT + horizon; if (total > 8192) total = 8192;
        for (int t = 0; t < total; t++) {
            snap[t][0] = a[0]; snap[t][1] = (uint64_t)phase;
            int nw = (n + t + 2 + 63) / 64; if (nw > MAXW) nw = MAXW;
            step(a, nw, W[phase] - '0'); phase = (phase + 1) % P;
        }
        // checkpoints
        int absT = -1, absW = 0; long absSize = 0;
        for (int t = 0; t < maxT && absT < 0; t += (t < 64 ? 4 : 16)) {
            // output word from t onward (white phases), minimal period
            int outs[2048]; int L = 0;
            for (int u = t; u < t + horizon && L < 2048; u++) if (W[snap[u][1]] == '0') outs[L++] = (int)(snap[u][0] & 1);
            int m = -1;
            for (int d = 1; d <= L / 3; d++) { int ok = 1; for (int i = d; i < L; i++) if (outs[i] != outs[i - d]) { ok = 0; break; } if (ok) { m = d; break; } }
            if (m < 0) continue;
            for (int wi = 0; wi < nwid; wi++) {
                int b = widths[wi]; uint64_t s = snap[t][0] & ((b >= 64) ? ~0ULL : ((1ULL << b) - 1));
                long r = closure_consistent(b, (int)snap[t][1], s, outs, m, limit);
                if (r > 0) { absT = t; absW = b; absSize = r; break; }
            }
        }
        if (absT >= 0) { cnt_abs++; wh[absW]++; if (absT > maxabs) maxabs = absT; int h = 0; while ((1 << (h + 1)) <= absT + 1) h++; tabs_hist[h]++;
            if (verbose >= 2 || (verbose == 1 && absW >= 24)) printf("case %ld phase0 %d cfg %s absorbed t=%d width=%d closure=%ld\n", tr, ph0, cfg, absT, absW, absSize); }
        else { cnt_un++; printf("UNCERTIFIED case %ld phase0 %d cfg %s\n", tr, ph0, cfg); }
    }
    printf("[range %ld..%ld] w=%s mode=%d n=%d cases=%ld certified-absorbed=%ld uncertified=%ld max certified absorption time %ld\n", c_lo, c_hi, W, mode, n, ncases, cnt_abs, cnt_un, maxabs);
    printf("  certificate widths:"); for (int i = 0; i < 64; i++) if (wh[i]) printf(" b=%d:%ld", i, wh[i]); printf("\n");
    printf("  absorption time histogram (log2 bins):"); for (int h = 0; h < 32; h++) if (tabs_hist[h]) printf(" [%d,%d):%ld", (1 << h) - 1, (1 << (h + 1)) - 1, tabs_hist[h]); printf("\n");
    return 0;
}
