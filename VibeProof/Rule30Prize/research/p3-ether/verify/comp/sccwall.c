// Verifier: terminal SCCs (minimal closed sets) of the strip graph driven by w (nodes (phase, strip of b cells),
// successors for right input z = 0, 1), and whether each admits a periodic labelling of column 1 at white
// phases ("good") or not ("bad"). Independent of the worker's scc_an.c.
// usage: sccbad w b
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int b, P; static int Wv[8]; static uint32_t M, mask;
static inline uint32_t sstep(uint32_t r, uint32_t a, uint32_t z) {
    return (((r << 1) | a) ^ (r | (r >> 1) | (z << (b - 1)))) & mask;
}
static int EA[3], EA1[3]; static inline void succ(uint32_t v, uint32_t o[2]) {
    uint32_t f = v / M, r = v % M, g = (f + 1) % P;
    o[0] = g * M + sstep(r, (uint32_t)EA[f], 0); o[1] = g * M + sstep(r, (uint32_t)EA[f], 1);
}
static long gcdl(long a, long c) { if (a < 0) a = -a; if (c < 0) c = -c; while (c) { long t = a % c; a = c; c = t; } return a; }
int main(int argc, char **argv) {
    P = 3; { static const char *e3[12] = {"001","001","011","110","010","010","110","101","100","100","101","011"}; int a = atoi(argv[1]); for (int f = 0; f < 3; f++) { EA[f] = e3[a % 12][f] - 48; EA1[f] = e3[(a + 1) % 12][f] - 48; Wv[f] = 1; } }
    b = atoi(argv[2]); M = 1u << b; mask = M - 1; uint32_t N = (uint32_t)P * M;
    int32_t *idx = malloc(4 * (size_t)N), *low = malloc(4 * (size_t)N), *comp = malloc(4 * (size_t)N);
    uint8_t *on = calloc(N, 1); uint32_t *stk = malloc(4 * (size_t)N), *cs = malloc(4 * (size_t)N); uint8_t *ci = malloc(N);
    for (uint32_t i = 0; i < N; i++) idx[i] = -1;
    int32_t cnt = 0, nc = 0; uint32_t sp = 0;
    for (uint32_t root = 0; root < N; root++) {
        if (idx[root] != -1) continue;
        uint32_t csp = 0; cs[csp] = root; ci[csp] = 0; csp++;
        idx[root] = low[root] = cnt++; stk[sp++] = root; on[root] = 1;
        while (csp) {
            uint32_t v = cs[csp - 1]; uint32_t o[2]; succ(v, o);
            if (ci[csp - 1] < 2) {
                uint32_t u = o[ci[csp - 1]]; ci[csp - 1]++;
                if (idx[u] == -1) { idx[u] = low[u] = cnt++; stk[sp++] = u; on[u] = 1; cs[csp] = u; ci[csp] = 0; csp++; }
                else if (on[u] && idx[u] < low[v]) low[v] = idx[u];
            } else {
                if (low[v] == idx[v]) { uint32_t u; do { u = stk[--sp]; on[u] = 0; comp[u] = nc; } while (u != v); nc++; }
                csp--;
                if (csp) { uint32_t p = cs[csp - 1]; if (low[v] < low[p]) low[p] = low[v]; }
            }
        }
    }
    uint8_t *term = malloc((size_t)nc); memset(term, 1, (size_t)nc);
    for (uint32_t v = 0; v < N; v++) { uint32_t o[2]; succ(v, o); if (comp[o[0]] != comp[v] || comp[o[1]] != comp[v]) term[comp[v]] = 0; }
    int nterm = 0; for (int c = 0; c < nc; c++) nterm += term[c];
    printf("w=%s b=%d: %d SCCs, %d terminal", argv[1], b, nc, nterm);
    // analyse each terminal SCC: BFS levels, period d, consistency of column 1 at white phases per class mod d
    int32_t *lev = idx; for (uint32_t i = 0; i < N; i++) lev[i] = -1;
    uint32_t *q = stk;
    for (int c = 0; c < nc; c++) if (term[c]) {
        uint32_t r0 = 0; while (comp[r0] != c) r0++;
        uint32_t qh = 0, qt = 0; q[qt++] = r0; lev[r0] = 0; long d = 0, size = 0;
        while (qh < qt) { uint32_t v = q[qh++]; size++; uint32_t o[2]; succ(v, o);
            for (int k = 0; k < 2; k++) { uint32_t u = o[k]; if (lev[u] < 0) { lev[u] = lev[v] + 1; q[qt++] = u; } else d = gcdl(d, (long)lev[v] + 1 - lev[u]); } }
        // class output table: -1 unset, 0/1 value, 2 conflict
        int8_t *cl = malloc((size_t)d); memset(cl, -1, (size_t)d); int bad = 0;
        for (uint32_t i = 0; i < qt; i++) { uint32_t v = q[i]; uint32_t f = v / M, r = v % M; if (Wv[f]) continue;
            int out = (int)(r & 1); long k = lev[v] % d; if (cl[k] < 0) cl[k] = (int8_t)out; else if (cl[k] != out) bad = 1; }
        { long viol = 0; for (uint32_t i = 0; i < qt; i++) { uint32_t v = q[i]; uint32_t f = v / M, r = v % M; if (!EA[f] && (int)(r & 1) != EA1[f]) viol++; } printf(" | terminal SCC size %ld, U-violating nodes %ld", size, viol); }
        free(cl);
    }
    printf("\n"); return 0;
}
