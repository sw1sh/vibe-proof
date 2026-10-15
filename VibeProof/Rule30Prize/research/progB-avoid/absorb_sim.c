// Simulate the w-driven right half (columns 1..) of rule 30 from finite configurations and measure when the
// width-b strip leaves R_b = {nodes that can reach the unique bad SCC B_b} (after which column 1 at white
// phases is eventually periodic: the strip can only end in a good SCC).
// Graph and SCCs are recomputed here (Tarjan), B_b = union of bad SCCs.
// usage: absorb_sim w b mode n trials maxT seed
//   mode 0: random configs with support exactly [1,n] (cell n = 1), random phase
//   mode 1: true rule-30 right half at time T=n (columns 1..T), driven by w from phase 0..P-1 (trials ignored)
//   mode 2: exhaustive: all configs with support within [1,n], all phases
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int P, b; static const char *W;
static inline int bitv(uint32_t s, int p, int cphi) { return p == 0 ? cphi : (int)((s >> (p - 1)) & 1); }
static int succ2(int phi, uint32_t s, uint32_t out[2]) {
    int cphi = W[phi] - '0';
    uint32_t base = 0;
    for (int p = 1; p < b; p++) {
        int v = bitv(s, p - 1, cphi) ^ (bitv(s, p, cphi) | bitv(s, p + 1, cphi));
        base |= (uint32_t)v << (p - 1);
    }
    if (bitv(s, b, cphi)) { out[0] = out[1] = base | ((uint32_t)(1 ^ bitv(s, b - 1, cphi)) << (b - 1)); return 1; }
    out[0] = base | ((uint32_t)bitv(s, b - 1, cphi) << (b - 1));
    out[1] = base | ((uint32_t)(1 ^ bitv(s, b - 1, cphi)) << (b - 1));
    return 2;
}
static inline uint32_t nodeid(int phi, uint32_t s) { return ((uint32_t)phi << b) | s; }
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static uint8_t *inR, *inB;
#define MAXW 1024
// one step of the driven right half; a[k] bit i = column 64k+i+1
static void step(uint64_t *a, int nw, int cphi) {
    uint64_t prevtop = (uint64_t)cphi; // bit for column 0
    for (int k = 0; k < nw; k++) {
        uint64_t cur = a[k];
        uint64_t left = (cur << 1) | prevtop;            // column p-1
        uint64_t right = (cur >> 1) | (k + 1 < nw ? (a[k + 1] << 63) : 0); // column p+1
        prevtop = cur >> 63;
        a[k] = left ^ (cur | right);
    }
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); b = atoi(argv[2]);
    int mode = atoi(argv[3]); int n = atoi(argv[4]); long trials = atol(argv[5]); int maxT = atoi(argv[6]);
    rng ^= (uint64_t)atol(argv[7]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    uint32_t N = (uint32_t)P << b;
    // Tarjan
    int32_t *idx = malloc(sizeof(int32_t) * N), *low = malloc(sizeof(int32_t) * N), *comp = malloc(sizeof(int32_t) * N);
    uint8_t *onst = calloc(N, 1); uint32_t *stk = malloc(sizeof(uint32_t) * N);
    uint32_t *wv = malloc(sizeof(uint32_t) * N); uint8_t *wi = malloc(N);
    for (uint32_t i = 0; i < N; i++) idx[i] = -1;
    int32_t counter = 0, ncomp = 0; uint32_t sp = 0;
    for (uint32_t root = 0; root < N; root++) {
        if (idx[root] != -1) continue;
        uint32_t wsp = 0; wv[wsp] = root; wi[wsp] = 0; wsp++;
        while (wsp) {
            uint32_t v = wv[wsp - 1]; int i = wi[wsp - 1];
            if (i == 0 && idx[v] == -1) { idx[v] = low[v] = counter++; stk[sp++] = v; onst[v] = 1; }
            uint32_t nb[2]; int nn = succ2(v >> b, v & ((1u << b) - 1), nb); int nphi = ((v >> b) + 1) % P;
            int pushed = 0;
            while (i < nn) {
                uint32_t u = nodeid(nphi, nb[i]); i++;
                if (idx[u] == -1) { wi[wsp - 1] = i; wv[wsp] = u; wi[wsp] = 0; wsp++; pushed = 1; break; }
                else if (onst[u] && idx[u] < low[v]) low[v] = idx[u];
            }
            if (pushed) continue;
            wi[wsp - 1] = i;
            if (low[v] == idx[v]) { uint32_t u; do { u = stk[--sp]; onst[u] = 0; comp[u] = ncomp; } while (u != v); ncomp++; }
            wsp--;
            if (wsp) { uint32_t pv = wv[wsp - 1]; if (low[v] < low[pv]) low[pv] = low[v]; }
        }
    }
    // classify: an SCC is bad iff inconsistent labelling. Simplified: reuse labelling via BFS per SCC.
    int32_t *csize = calloc(ncomp, sizeof(int32_t)); uint8_t *nontriv = calloc(ncomp, 1);
    for (uint32_t v = 0; v < N; v++) csize[comp[v]]++;
    for (uint32_t v = 0; v < N; v++) { uint32_t nb[2]; int nn = succ2(v >> b, v & ((1u << b) - 1), nb);
        for (int i = 0; i < nn; i++) if (comp[nodeid(((v >> b) + 1) % P, nb[i])] == comp[v]) nontriv[comp[v]] = 1; }
    uint32_t *first = malloc(sizeof(uint32_t) * ncomp); for (int c = 0; c < ncomp; c++) first[c] = UINT32_MAX;
    for (uint32_t v = 0; v < N; v++) if (first[comp[v]] == UINT32_MAX) first[comp[v]] = v;
    int32_t *pos = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) pos[i] = -1;
    uint32_t *q = malloc(sizeof(uint32_t) * N); uint32_t *par = malloc(sizeof(uint32_t) * N);
    int32_t *vis = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) vis[i] = -1;
    uint32_t *path = malloc(sizeof(uint32_t) * N); int *word = malloc(sizeof(int) * N);
    uint8_t *isbad = calloc(ncomp, 1);
    for (int c = 0; c < ncomp; c++) {
        if (!nontriv[c]) continue;
        uint32_t st = first[c]; uint32_t qh = 0, qt = 0; q[qt++] = st; vis[st] = c; par[st] = UINT32_MAX; uint32_t back = UINT32_MAX;
        while (qh < qt && back == UINT32_MAX) { uint32_t xx = q[qh++]; uint32_t nb[2]; int nn = succ2(xx >> b, xx & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) { uint32_t yy = nodeid(((xx >> b) + 1) % P, nb[i]); if (comp[yy] != c) continue;
                if (yy == st) { back = xx; break; } if (vis[yy] != c) { vis[yy] = c; par[yy] = xx; q[qt++] = yy; } } }
        int plen = 0; { uint32_t xx = back; while (xx != st) { path[plen++] = xx; xx = par[xx]; } path[plen++] = st; }
        for (int i = 0; i < plen / 2; i++) { uint32_t t = path[i]; path[i] = path[plen - 1 - i]; path[plen - 1 - i] = t; }
        int L = 0; for (int i = 0; i < plen; i++) { uint32_t xx = path[i]; if (W[xx >> b] == '0') word[L++] = xx & 1; }
        int m = L; for (int d = 1; d <= L; d++) if (L % d == 0) { int ok = 1; for (int i = d; i < L; i++) if (word[i] != word[i - d]) { ok = 0; break; } if (ok) { m = d; break; } }
        qh = 0; qt = 0; q[qt++] = st; pos[st] = 0; int good = 1;
        while (qh < qt && good) { uint32_t xx = q[qh++]; int o = (W[xx >> b] == '0') ? (int)(xx & 1) : -1; int np;
            if (o >= 0) { if (o != word[pos[xx] % m]) { good = 0; break; } np = (pos[xx] + 1) % m; } else np = pos[xx];
            uint32_t nb[2]; int nn = succ2(xx >> b, xx & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) { uint32_t yy = nodeid(((xx >> b) + 1) % P, nb[i]); if (comp[yy] != c) continue;
                if (pos[yy] >= 0) { if (pos[yy] != np) { good = 0; break; } } else { pos[yy] = np; q[qt++] = yy; } } }
        if (!good) isbad[c] = 1;
    }
    inB = calloc(N, 1); inR = calloc(N, 1);
    for (uint32_t v = 0; v < N; v++) if (isbad[comp[v]]) inB[v] = 1;
    // backward closure: R = nodes that can reach B. iterate in reverse topological order: simple fixpoint loop
    memcpy(inR, inB, N);
    int changed = 1, rounds = 0;
    while (changed) { changed = 0; rounds++;
        for (uint32_t v = 0; v < N; v++) if (!inR[v]) { uint32_t nb[2]; int nn = succ2(v >> b, v & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) if (inR[nodeid(((v >> b) + 1) % P, nb[i])]) { inR[v] = 1; changed = 1; break; } } }
    long nB = 0, nR = 0; for (uint32_t v = 0; v < N; v++) { nB += inB[v]; nR += inR[v]; }
    fprintf(stderr, "w=%s b=%d |B|=%ld |R|=%ld (fixpoint rounds %d)\n", W, b, nB, nR, rounds);
    // simulation
    static uint64_t a[MAXW];
    long hist[64] = {0}; long maxabs = -1; long catBper = 0, catBaper = 0, catRB = 0; long survivors = 0; long total = 0;
    long ncases = mode == 2 ? ((long)1 << n) * P : (mode == 1 ? P : trials);
    for (long tr = 0; tr < ncases; tr++) {
        memset(a, 0, sizeof(a));
        int phase;
        static char cfgstr[4096]; int phase0 = 0;
        if (mode == 0) { for (int p = 1; p <= n; p++) { int bit = (p == n || (xr() & 1)); if (bit) a[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63); cfgstr[p - 1] = '0' + bit; } cfgstr[n] = 0; phase = xr() % P; }
        else if (mode == 2) { long cfg = tr / P; phase = tr % P; for (int p = 1; p <= n; p++) if ((cfg >> (p - 1)) & 1) a[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63); }
        else { // true rule 30 at time n: compute full row then take columns 1..n
            static uint64_t row[2 * MAXW + 2]; int RW = (2 * n + 1 + 63) / 64 + 1; memset(row, 0, sizeof(row));
            // row bit i = position i - n
            row[n >> 6] |= 1ULL << (n & 63);
            for (int t = 0; t < n; t++) { static uint64_t nr[2 * MAXW + 2];
                for (int k = 0; k < RW; k++) { uint64_t cur = row[k]; uint64_t l = (cur << 1) | (k ? row[k - 1] >> 63 : 0); uint64_t r = (cur >> 1) | (k + 1 < RW ? row[k + 1] << 63 : 0); nr[k] = l ^ (cur | r); }
                memcpy(row, nr, sizeof(uint64_t) * RW); }
            for (int p = 1; p <= n; p++) { int i = p + n; if ((row[i >> 6] >> (i & 63)) & 1) a[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63); }
            phase = tr;
        }
        phase0 = phase; int absT = -1; int everB = 0; static uint32_t hs[1 << 20]; int nowB = 0;
        for (int t = 0; t < maxT; t++) {
            uint32_t s = (uint32_t)(a[0] & ((1u << b) - 1));
            uint32_t v = nodeid(phase, s);
            if (t < (1 << 20)) hs[t] = v;
            nowB = inB[v];
            if (inB[v]) everB = 1;
            if (!inR[v]) { absT = t; break; }
            int nw = (n + t + 2 + 63) / 64; if (nw > MAXW) nw = MAXW;
            step(a, nw, W[phase] - '0'); phase = (phase + 1) % P;
        }
        total++;
        if (absT < 0) { survivors++;
            // period of the strip-node sequence over the last half
            int Tn = maxT < (1 << 20) ? maxT : (1 << 20); int per = -1;
            for (int d = 1; d <= Tn / 4; d++) { int ok = 1; for (int t = Tn / 2; t + d < Tn; t++) if (hs[t] != hs[t + d]) { ok = 0; break; } if (ok) { per = d; break; } }
            if (nowB && per > 0) catBper++; else if (nowB) { catBaper++; printf("APERIODIC-IN-B survivor case %ld\n", tr); } else catRB++;
            if (mode == 0) printf("SURV cfg %s phase0 %d nowB %d per %d\n", cfgstr, phase0, nowB, per);
            if (mode == 1) printf("survivor case %ld (everB=%d nowB=%d) strip period over 2nd half: %d\n", tr, everB, nowB, per); }
        else { int h = 0; while ((1L << (h + 1)) <= absT + 1 && h < 62) h++; hist[h]++; if (absT > maxabs) maxabs = absT; }
        if (mode == 1) printf("T=%d phase %ld: absorbed at %d (everB=%d)\n", n, tr, absT, everB);
    }
    printf("cases %ld survivors(maxT=%d) %ld [in B periodic %ld, in B aperiodic %ld, in R-B %ld] max absorption time %ld\n", total, maxT, survivors, catBper, catBaper, catRB, maxabs);
    for (int h = 0; h < 40; h++) if (hist[h]) printf("  abs time in [%ld,%ld): %ld\n", (1L << h) - 1, (1L << (h + 1)) - 1, hist[h]);
    return 0;
}
