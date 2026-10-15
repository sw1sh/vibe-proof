// Strip relaxation of "column 0 = w^inf": columns 1..b of rule 30, column b+1 free.
// Node = (phase, strip state). Output at node = col_1 if w[phase]=='0' else none.
// Checks whether every nontrivial SCC has a consistent position labelling (all cycle outputs are powers of
// one primitive word) => every infinite path has eventually periodic output (col_1 on zeros of c).
// Prints the number of bad SCCs and their sizes.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int P, b; static const char *W;
static inline int bitv(uint32_t s, int p, int cphi) { return p == 0 ? cphi : (int)((s >> (p - 1)) & 1); }
static int succ(int phi, uint32_t s, uint32_t out[2]) {
    int cphi = W[phi] - '0';
    uint32_t base = 0;
    for (int p = 1; p < b; p++) {
        int v = bitv(s, p - 1, cphi) ^ (bitv(s, p, cphi) | bitv(s, p + 1, cphi));
        base |= (uint32_t)v << (p - 1);
    }
    if (bitv(s, b, cphi)) { out[0] = base | ((uint32_t)(1 ^ bitv(s, b - 1, cphi)) << (b - 1)); return 1; }
    out[0] = base; out[1] = base | (1u << (b - 1)); return 2;
}
static inline uint32_t nodeid(int phi, uint32_t s) { return ((uint32_t)phi << b) | s; }
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); b = atoi(argv[2]);
    int verbose = argc > 3 ? atoi(argv[3]) : 0;
    uint32_t N = (uint32_t)P << b;
    int32_t *idx = malloc(sizeof(int32_t) * N), *low = malloc(sizeof(int32_t) * N), *comp = malloc(sizeof(int32_t) * N);
    uint8_t *onst = calloc(N, 1);
    uint32_t *stk = malloc(sizeof(uint32_t) * N);
    uint32_t *wv = malloc(sizeof(uint32_t) * N); uint8_t *wi = malloc(N);
    for (uint32_t i = 0; i < N; i++) idx[i] = -1;
    int32_t counter = 0, ncomp = 0; uint32_t sp = 0;
    for (uint32_t root = 0; root < N; root++) {
        if (idx[root] != -1) continue;
        uint32_t wsp = 0; wv[wsp] = root; wi[wsp] = 0; wsp++;
        while (wsp) {
            uint32_t v = wv[wsp - 1]; int i = wi[wsp - 1];
            if (i == 0 && idx[v] == -1) { idx[v] = low[v] = counter++; stk[sp++] = v; onst[v] = 1; }
            uint32_t nb[2]; int phi = v >> b; uint32_t s = v & ((1u << b) - 1);
            int nn = succ(phi, s, nb); int nphi = (phi + 1) % P;
            int pushed = 0;
            while (i < nn) {
                uint32_t u = nodeid(nphi, nb[i]); i++;
                if (idx[u] == -1) { wi[wsp - 1] = i; wv[wsp] = u; wi[wsp] = 0; wsp++; pushed = 1; break; }
                else if (onst[u] && idx[u] < low[v]) low[v] = idx[u];
            }
            if (pushed) continue;
            wi[wsp - 1] = i;
            if (low[v] == idx[v]) {
                uint32_t u;
                do { u = stk[--sp]; onst[u] = 0; comp[u] = ncomp; } while (u != v);
                ncomp++;
            }
            wsp--;
            if (wsp) { uint32_t pv = wv[wsp - 1]; if (low[v] < low[pv]) low[pv] = low[v]; }
        }
    }
    // component sizes and nontriviality
    int32_t *csize = calloc(ncomp, sizeof(int32_t)); uint8_t *nontriv = calloc(ncomp, 1);
    for (uint32_t v = 0; v < N; v++) {
        csize[comp[v]]++;
        uint32_t nb[2]; int nn = succ(v >> b, v & ((1u << b) - 1), nb);
        for (int i = 0; i < nn; i++) { uint32_t u = nodeid(((v >> b) + 1) % P, nb[i]); if (comp[u] == comp[v] && (csize[comp[v]] > 1 || u == v)) nontriv[comp[v]] = 1; }
    }
    // second pass for nontriviality (size>1 comps are nontrivial)
    for (int c = 0; c < ncomp; c++) if (csize[c] > 1) nontriv[c] = 1;
    // per component: find a cycle from some member, take primitive root of its output, BFS-label positions
    int32_t *pos = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) pos[i] = -1;
    uint32_t *q = malloc(sizeof(uint32_t) * N); uint32_t *par = malloc(sizeof(uint32_t) * N);
    int32_t *vis = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) vis[i] = -1;
    uint32_t *path = malloc(sizeof(uint32_t) * N); int *word = malloc(sizeof(int) * N);
    uint32_t *first = malloc(sizeof(uint32_t) * ncomp); for (int c = 0; c < ncomp; c++) first[c] = UINT32_MAX;
    for (uint32_t v = 0; v < N; v++) if (first[comp[v]] == UINT32_MAX) first[comp[v]] = v;
    int nbad = 0, ngood = 0; long badnodes = 0;
    for (int c = 0; c < ncomp; c++) {
        if (!nontriv[c]) continue;
        uint32_t st = first[c];
        uint32_t qh = 0, qt = 0; q[qt++] = st; vis[st] = c; par[st] = UINT32_MAX; uint32_t back = UINT32_MAX;
        while (qh < qt && back == UINT32_MAX) {
            uint32_t x = q[qh++]; uint32_t nb[2]; int nn = succ(x >> b, x & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) {
                uint32_t y = nodeid(((x >> b) + 1) % P, nb[i]);
                if (comp[y] != c) continue;
                if (y == st) { back = x; break; }
                if (vis[y] != c) { vis[y] = c; par[y] = x; q[qt++] = y; }
            }
        }
        if (back == UINT32_MAX) { fprintf(stderr, "no cycle found in nontrivial SCC?\n"); return 1; }
        int plen = 0;
        { uint32_t x = back; while (x != st) { path[plen++] = x; x = par[x]; } path[plen++] = st; }
        for (int i = 0; i < plen / 2; i++) { uint32_t t = path[i]; path[i] = path[plen - 1 - i]; path[plen - 1 - i] = t; }
        int L = 0;
        for (int i = 0; i < plen; i++) { uint32_t x = path[i]; if (W[x >> b] == '0') word[L++] = x & 1; }
        int m = L;
        for (int d = 1; d <= L; d++) if (L % d == 0) { int ok = 1; for (int i = d; i < L; i++) if (word[i] != word[i - d]) { ok = 0; break; } if (ok) { m = d; break; } }
        qh = 0; qt = 0; q[qt++] = st; pos[st] = 0; int good = 1;
        while (qh < qt && good) {
            uint32_t x = q[qh++]; int o = (W[x >> b] == '0') ? (int)(x & 1) : -1; int np;
            if (o >= 0) { if (o != word[pos[x] % m]) { good = 0; break; } np = (pos[x] + 1) % m; } else np = pos[x];
            uint32_t nb[2]; int nn = succ(x >> b, x & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) {
                uint32_t y = nodeid(((x >> b) + 1) % P, nb[i]);
                if (comp[y] != c) continue;
                if (pos[y] >= 0) { if (pos[y] != np) { good = 0; break; } }
                else { pos[y] = np; q[qt++] = y; }
            }
        }
        if (good) ngood++; else { nbad++; badnodes += csize[c]; if (verbose) printf("  bad SCC size %d\n", csize[c]); }
    }
    printf("w=%s b=%d nodes=%u SCCs(nontrivial): good=%d bad=%d (bad nodes %ld)\n", W, b, N, ngood, nbad, badnodes);
    return 0;
}
