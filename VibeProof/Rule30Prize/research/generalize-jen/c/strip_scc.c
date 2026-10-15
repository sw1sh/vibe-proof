// Adversarial strip model of the right half of rule 30 driven by a periodic word w at column 0.
// State: columns 1..K (bit i <-> column i+1); column K+1 is chosen freely each step.
// 1. Limit sets R(ph): states reachable at phase ph after arbitrarily many periods from ALL states.
// 2. Step graph on (ph, s), s in R(ph); SCCs (Tarjan); in each nontrivial SCC compute the period g and
//    check that column 1 is a function of the cyclic class at zero phases (e-criterion) / all phases (d).
// Output: forcedE forcedD (col1 constant per phase in the limit), sccE sccD (SCC criterion).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int K, P; static uint32_t N, MASK; static int W[64];
static inline uint32_t succ(int ph, uint32_t s, int a) {
    return ((((s << 1) | (uint32_t)W[ph]) ^ (s | (s >> 1) | ((uint32_t)a << (K - 1))))) & MASK;
}
static long gcdl(long a, long b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { long t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: w K\n"); return 1; }
    const char *w = argv[1]; K = atoi(argv[2]); P = (int)strlen(w);
    for (int i = 0; i < P; i++) W[i] = w[i] - '0';
    N = 1u << K; MASK = N - 1;
    uint8_t *R = malloc((size_t)P * N); memset(R, 1, (size_t)P * N);
    uint8_t *tmp = malloc(N);
    int changed = 1, iters = 0;
    while (changed) {
        changed = 0; iters++;
        for (int ph = 0; ph < P; ph++) {
            int nx = (ph + 1) % P; memset(tmp, 0, N);
            uint8_t *Rp = R + (size_t)ph * N, *Rn = R + (size_t)nx * N;
            for (uint32_t s = 0; s < N; s++) if (Rp[s]) { tmp[succ(ph, s, 0)] = 1; tmp[succ(ph, s, 1)] = 1; }
            for (uint32_t s = 0; s < N; s++) { uint8_t v = tmp[s] & Rn[s]; if (v != Rn[s]) changed = 1; Rn[s] = v; }
        }
    }
    // forced per phase
    int forcedE = 1, forcedD = 1; char col1[65];
    for (int ph = 0; ph < P; ph++) {
        int h0 = 0, h1 = 0; uint8_t *Rp = R + (size_t)ph * N;
        for (uint32_t s = 0; s < N; s++) if (Rp[s]) { if (s & 1) h1 = 1; else h0 = 1; }
        col1[ph] = (h0 && h1) ? '-' : (h0 ? '0' : (h1 ? '1' : 'x'));
        if (h0 && h1) { forcedD = 0; if (W[ph] == 0) forcedE = 0; }
    }
    col1[P] = 0;
    // Tarjan (iterative)
    size_t M = (size_t)P * N;
    int32_t *idx = malloc(M * 4), *low = malloc(M * 4), *comp = malloc(M * 4);
    uint32_t *stk = malloc(M * 4), *cs_node = malloc(M * 4); uint8_t *cs_edge = malloc(M), *onstk = calloc(M, 1);
    for (size_t i = 0; i < M; i++) { idx[i] = -1; comp[i] = -1; }
    int32_t counter = 0, ncomp = 0; size_t sp = 0;
    for (size_t root = 0; root < M; root++) {
        if (!R[root] || idx[root] >= 0) continue;
        size_t csp = 0; cs_node[csp] = (uint32_t)root; cs_edge[csp] = 0; csp++;
        idx[root] = low[root] = counter++; stk[sp++] = (uint32_t)root; onstk[root] = 1;
        while (csp) {
            uint32_t v = cs_node[csp - 1]; int ph = v / N; uint32_t s = v % N;
            if (cs_edge[csp - 1] < 2) {
                int a = cs_edge[csp - 1]++;
                uint32_t u = (uint32_t)(((ph + 1) % P) * N + succ(ph, s, a));
                if (idx[u] < 0) { idx[u] = low[u] = counter++; stk[sp++] = u; onstk[u] = 1; cs_node[csp] = u; cs_edge[csp] = 0; csp++; }
                else if (onstk[u] && idx[u] < low[v]) low[v] = idx[u];
            } else {
                if (low[v] == idx[v]) {
                    uint32_t x; do { x = stk[--sp]; onstk[x] = 0; comp[x] = ncomp; } while (x != v);
                    ncomp++;
                }
                csp--;
                if (csp) { uint32_t par = cs_node[csp - 1]; if (low[v] < low[par]) low[par] = low[v]; }
            }
        }
    }
    // per-component analysis: BFS distances within component
    int32_t *dist = malloc(M * 4); for (size_t i = 0; i < M; i++) dist[i] = -1;
    uint32_t *queue = malloc(M * 4);
    long *gcomp = calloc(ncomp, sizeof(long)); int32_t *croot = malloc(ncomp * 4); for (int c = 0; c < ncomp; c++) croot[c] = -1;
    int32_t *csize = calloc(ncomp, 4);
    for (size_t v = 0; v < M; v++) if (R[v]) { csize[comp[v]]++; if (croot[comp[v]] < 0) croot[comp[v]] = (int32_t)v; }
    int sccE = 1, sccD = 1, nontriv = 0; long maxg = 0;
    for (int c = 0; c < ncomp; c++) {
        uint32_t r = (uint32_t)croot[c];
        // nontrivial? size>1, or self loop
        int nt = csize[c] > 1;
        if (!nt) { int ph = r / N; uint32_t s = r % N; for (int a = 0; a < 2; a++) if ((uint32_t)(((ph + 1) % P) * N + succ(ph, s, a)) == r) nt = 1; }
        if (!nt) continue;
        nontriv++;
        size_t qh = 0, qt = 0; queue[qt++] = r; dist[r] = 0; long g = 0;
        while (qh < qt) {
            uint32_t v = queue[qh++]; int ph = v / N; uint32_t s = v % N;
            for (int a = 0; a < 2; a++) {
                uint32_t u = (uint32_t)(((ph + 1) % P) * N + succ(ph, s, a));
                if (comp[u] != c) continue;
                if (dist[u] < 0) { dist[u] = dist[v] + 1; queue[qt++] = u; }
                else g = gcdl(g, (long)dist[v] + 1 - dist[u]);
            }
        }
        if (g == 0) g = 1; // should not happen for nontrivial
        if (g > maxg) maxg = g;
        gcomp[c] = g;
        // check output function of class
        // classes up to g; store seen values: 0 none, 1 saw0, 2 saw1, 3 both
        uint8_t *seenE = calloc(g, 1), *seenD = calloc(g, 1);
        for (size_t i = 0; i < qt; i++) {
            uint32_t v = queue[i]; int ph = v / N; uint32_t s = v % N; long cl = dist[v] % g;
            uint8_t bit = (s & 1) ? 2 : 1;
            seenD[cl] |= bit; if (W[ph] == 0) seenE[cl] |= bit;
        }
        for (long cl = 0; cl < g; cl++) { if (seenD[cl] == 3) sccD = 0; if (seenE[cl] == 3) sccE = 0; }
        free(seenE); free(seenD);
    }
    long tot = 0; for (size_t v = 0; v < M; v++) tot += R[v];
    printf("%s K=%d iters=%d limitStates=%ld forcedE=%d forcedD=%d sccE=%d sccD=%d nontrivSCC=%d maxg=%ld col1=%s\n",
           w, K, iters, tot, forcedE, forcedD, sccE, sccD, nontriv, maxg, col1);
    return 0;
}
