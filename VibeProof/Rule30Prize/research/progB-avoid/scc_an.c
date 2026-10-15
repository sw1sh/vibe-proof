// Strip graph analysis for rule 30 right half driven by column 0 = w^inf.
// Node = (phase, s), s = columns 1..b (bit p-1 = column p). Input x = column b+1.
// Output at node = col_1 if w[phase]=='0'.
// Computes SCCs (Tarjan, iterative), classifies nontrivial SCCs as good (consistent periodic labelling of
// the output) or bad, and for bad SCCs reports: size, # nodes with input-relevant (col b = 0) and both
// successors inside, forced-input nodes, entropy estimate (power iteration on induced subgraph).
// Optional: dump the union of bad SCCs as "phase state compid" lines.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
static int P, b; static const char *W;
static inline int bitv(uint32_t s, int p, int cphi) { return p == 0 ? cphi : (int)((s >> (p - 1)) & 1); }
// out[i] = successor with input x=i (when col b == 1 both equal); returns 1 if input irrelevant, 2 otherwise
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
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: w b [dumpfile]\n"); return 1; }
    W = argv[1]; P = strlen(W); b = atoi(argv[2]);
    FILE *dumpf = argc > 3 ? fopen(argv[3], "w") : NULL;
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
            int nn = succ2(phi, s, nb); int nphi = (phi + 1) % P;
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
    int32_t *csize = calloc(ncomp, sizeof(int32_t)); uint8_t *nontriv = calloc(ncomp, 1);
    for (uint32_t v = 0; v < N; v++) csize[comp[v]]++;
    for (uint32_t v = 0; v < N; v++) {
        uint32_t nb[2]; int nn = succ2(v >> b, v & ((1u << b) - 1), nb);
        for (int i = 0; i < nn; i++) { uint32_t u = nodeid(((v >> b) + 1) % P, nb[i]); if (comp[u] == comp[v]) nontriv[comp[v]] = 1; }
    }
    int32_t *pos = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) pos[i] = -1;
    uint32_t *q = malloc(sizeof(uint32_t) * N); uint32_t *par = malloc(sizeof(uint32_t) * N);
    int32_t *vis = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) vis[i] = -1;
    uint32_t *path = malloc(sizeof(uint32_t) * N); int *word = malloc(sizeof(int) * N);
    uint32_t *first = malloc(sizeof(uint32_t) * ncomp); for (int c = 0; c < ncomp; c++) first[c] = UINT32_MAX;
    for (uint32_t v = 0; v < N; v++) if (first[comp[v]] == UINT32_MAX) first[comp[v]] = v;
    uint8_t *isbad = calloc(ncomp, 1);
    int nbad = 0, ngood = 0; long badnodes = 0, goodnodes = 0;
    double *x = malloc(sizeof(double) * N), *y = malloc(sizeof(double) * N);
    for (int c = 0; c < ncomp; c++) {
        if (!nontriv[c]) continue;
        uint32_t st = first[c];
        uint32_t qh = 0, qt = 0; q[qt++] = st; vis[st] = c; par[st] = UINT32_MAX; uint32_t back = UINT32_MAX;
        while (qh < qt && back == UINT32_MAX) {
            uint32_t xx = q[qh++]; uint32_t nb[2]; int nn = succ2(xx >> b, xx & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) {
                uint32_t yy = nodeid(((xx >> b) + 1) % P, nb[i]);
                if (comp[yy] != c) continue;
                if (yy == st) { back = xx; break; }
                if (vis[yy] != c) { vis[yy] = c; par[yy] = xx; q[qt++] = yy; }
            }
        }
        if (back == UINT32_MAX) { fprintf(stderr, "no cycle found in nontrivial SCC?\n"); return 1; }
        int plen = 0;
        { uint32_t xx = back; while (xx != st) { path[plen++] = xx; xx = par[xx]; } path[plen++] = st; }
        for (int i = 0; i < plen / 2; i++) { uint32_t t = path[i]; path[i] = path[plen - 1 - i]; path[plen - 1 - i] = t; }
        int L = 0;
        for (int i = 0; i < plen; i++) { uint32_t xx = path[i]; if (W[xx >> b] == '0') word[L++] = xx & 1; }
        int m = L;
        for (int d = 1; d <= L; d++) if (L % d == 0) { int ok = 1; for (int i = d; i < L; i++) if (word[i] != word[i - d]) { ok = 0; break; } if (ok) { m = d; break; } }
        qh = 0; qt = 0; q[qt++] = st; pos[st] = 0; int good = 1;
        while (qh < qt && good) {
            uint32_t xx = q[qh++]; int o = (W[xx >> b] == '0') ? (int)(xx & 1) : -1; int np;
            if (o >= 0) { if (o != word[pos[xx] % m]) { good = 0; break; } np = (pos[xx] + 1) % m; } else np = pos[xx];
            uint32_t nb[2]; int nn = succ2(xx >> b, xx & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) {
                uint32_t yy = nodeid(((xx >> b) + 1) % P, nb[i]);
                if (comp[yy] != c) continue;
                if (pos[yy] >= 0) { if (pos[yy] != np) { good = 0; break; } }
                else { pos[yy] = np; q[qt++] = yy; }
            }
        }
        if (good) { ngood++; goodnodes += csize[c]; printf("  good SCC size %d outword ", csize[c]); for (int i = 0; i < m; i++) printf("%d", word[i]); printf("\n"); }
        else { nbad++; badnodes += csize[c]; isbad[c] = 1; }
    }
    // analyse bad SCCs
    for (int c = 0; c < ncomp; c++) {
        if (!isbad[c]) continue;
        long n2 = 0, nirr = 0, nforced = 0, nforced0 = 0, nforced1 = 0;
        for (uint32_t v = 0; v < N; v++) if (comp[v] == c) {
            uint32_t nb[2]; int nn = succ2(v >> b, v & ((1u << b) - 1), nb); int nph = ((v >> b) + 1) % P;
            if (nn == 1) { nirr++; continue; }
            int in0 = comp[nodeid(nph, nb[0])] == c, in1 = comp[nodeid(nph, nb[1])] == c;
            if (in0 && in1) n2++; else { nforced++; if (in0) nforced0++; else nforced1++; }
        }
        // entropy: power iteration on the induced subgraph (per step), restricted to members
        uint32_t nm = 0; for (uint32_t v = 0; v < N; v++) if (comp[v] == c) q[nm++] = v;
        for (uint32_t k = 0; k < nm; k++) x[q[k]] = 1.0 / nm;
        double lam = 0;
        for (int it = 0; it < 400; it++) {
            for (uint32_t k = 0; k < nm; k++) y[q[k]] = 0;
            for (uint32_t k = 0; k < nm; k++) { uint32_t v = q[k]; if (x[v] == 0) continue;
                uint32_t nb[2]; int nn = succ2(v >> b, v & ((1u << b) - 1), nb); int nph = ((v >> b) + 1) % P;
                for (int i = 0; i < nn; i++) { uint32_t u = nodeid(nph, nb[i]); if (comp[u] == c) y[u] += x[v]; }
            }
            double s = 0; for (uint32_t k = 0; k < nm; k++) s += y[q[k]];
            if (s == 0) { lam = 0; break; }
            for (uint32_t k = 0; k < nm; k++) x[q[k]] = y[q[k]] / s;
            lam = s;
        }
        printf("  BAD SCC size %d: input-irrelevant %ld, free(both in) %ld, forced %ld (to 0: %ld, to 1: %ld), growth/step ~ %.4f\n",
               csize[c], nirr, n2, nforced, nforced0, nforced1, lam);
        if (dumpf) for (uint32_t v = 0; v < N; v++) if (comp[v] == c) fprintf(dumpf, "%u %u %d\n", v >> b, v & ((1u << b) - 1), c);
    }
    printf("w=%s b=%d nodes=%u SCCs(nontrivial): good=%d (nodes %ld) bad=%d (nodes %ld)\n", W, b, N, ngood, goodnodes, nbad, badnodes);
    if (dumpf) fclose(dumpf);
    return 0;
}
