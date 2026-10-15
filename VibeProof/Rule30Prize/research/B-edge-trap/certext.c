// Strip relaxation for "column 0 = w^inf": nodes (phase, strip of columns 1..b), column b+1 free.
// Output at node = col_1 if w[phase]=='0'.
// SAFE = nodes that cannot reach a "bad" nontrivial SCC (one without a consistent position labelling).
// Once the true right half is in SAFE, column 1 at the white phases is eventually periodic.
// Writes SAFE as a byte array file (1 = safe) of size P<<b, and per-node SCC good-label info is not needed.
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
    if (argc < 4) { fprintf(stderr, "usage: safe w b outfile\n"); return 1; }
    W = argv[1]; P = strlen(W); b = atoi(argv[2]);
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
    int32_t *csize = calloc(ncomp, sizeof(int32_t)); uint8_t *nontriv = calloc(ncomp, 1);
    for (uint32_t v = 0; v < N; v++) csize[comp[v]]++;
    for (uint32_t v = 0; v < N; v++) {
        uint32_t nb[2]; int nn = succ(v >> b, v & ((1u << b) - 1), nb);
        for (int i = 0; i < nn; i++) { uint32_t u = nodeid(((v >> b) + 1) % P, nb[i]); if (u == v) nontriv[comp[v]] = 1; }
    }
    for (int c = 0; c < ncomp; c++) if (csize[c] > 1) nontriv[c] = 1;
    // nodes grouped by component
    uint32_t *start = calloc(ncomp + 1, sizeof(uint32_t)); uint32_t *ord = malloc(sizeof(uint32_t) * N);
    for (uint32_t v = 0; v < N; v++) start[comp[v] + 1]++;
    for (int c = 0; c < ncomp; c++) start[c + 1] += start[c];
    { uint32_t *fill = malloc(sizeof(uint32_t) * (ncomp + 1)); memcpy(fill, start, sizeof(uint32_t) * (ncomp + 1));
      for (uint32_t v = 0; v < N; v++) ord[fill[comp[v]]++] = v; free(fill); }
    int32_t *pos = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) pos[i] = -1;
    uint32_t *q = malloc(sizeof(uint32_t) * N); uint32_t *par = malloc(sizeof(uint32_t) * N);
    int32_t *vis = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) vis[i] = -1;
    uint32_t *path = malloc(sizeof(uint32_t) * N); int *word = malloc(sizeof(int) * N);
    uint8_t *bad = calloc(ncomp, 1);
    int nbad = 0, ngood = 0;
    for (int c = 0; c < ncomp; c++) {
        if (!nontriv[c]) continue;
        uint32_t st = ord[start[c]];
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
        if (L == 0) { bad[c] = 1; nbad++; continue; } // no white phase on the cycle: cannot happen if w has a 0
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
        if (good) ngood++; else { nbad++; bad[c] = 1; }
    }
    // canReachBad in Tarjan completion order (successor SCCs complete earlier)
    uint8_t *crb = calloc(ncomp, 1);
    for (int c = 0; c < ncomp; c++) {
        if (bad[c]) { crb[c] = 1; continue; }
        for (uint32_t k = start[c]; k < start[c + 1] && !crb[c]; k++) {
            uint32_t v = ord[k]; uint32_t nb[2]; int nn = succ(v >> b, v & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) { uint32_t u = nodeid(((v >> b) + 1) % P, nb[i]); if (comp[u] != c && crb[comp[u]]) { crb[c] = 1; break; } }
        }
    }

    // certificate extraction: for each listed start node x0, BFS to the first node y of a bad SCC that has
    // two successors inside its SCC; then shortest return paths from each successor back to y inside the SCC.
    uint8_t *pin = malloc(N); uint32_t *qq = malloc(sizeof(uint32_t) * N);
    int32_t *mark = malloc(sizeof(int32_t) * N); for (uint32_t i = 0; i < N; i++) mark[i] = -1;
    FILE *g = fopen(argv[4], "r"); unsigned ph0, st0; int qid = 0;
    while (fscanf(g, "%u %u", &ph0, &st0) == 2) {
        qid++;
        uint32_t x0 = nodeid(ph0, st0); uint32_t qh = 0, qt = 0; qq[qt++] = x0; mark[x0] = qid * 3; par[x0] = UINT32_MAX;
        uint32_t y = UINT32_MAX;
        while (qh < qt && y == UINT32_MAX) {
            uint32_t v = qq[qh++];
            if (bad[comp[v]]) { uint32_t nb[2]; int nn = succ(v >> b, v & ((1u << b) - 1), nb); int inside = 0;
                for (int i = 0; i < nn; i++) if (comp[nodeid(((v >> b) + 1) % P, nb[i])] == comp[v]) inside++;
                if (inside == 2) { y = v; break; } }
            uint32_t nb[2]; int nn = succ(v >> b, v & ((1u << b) - 1), nb);
            for (int i = 0; i < nn; i++) { uint32_t u = nodeid(((v >> b) + 1) % P, nb[i]); if (mark[u] != qid * 3) { mark[u] = qid * 3; par[u] = v; pin[u] = (uint8_t)i; qq[qt++] = u; } }
        }
        if (y == UINT32_MAX) { printf("CERT %u %u none\n", ph0, st0); continue; }
        // path x0 -> y as input bits (index of successor; when only one successor, 0)
        static uint8_t pathbits[1 << 20]; int pl = 0; { uint32_t v = y; while (v != x0) { pathbits[pl++] = pin[v]; v = par[v]; } }
        printf("CERT %u %u path ", ph0, st0); if (pl == 0) printf("-"); for (int i = pl - 1; i >= 0; i--) printf("%d", pathbits[i]);
        // helper lambdas emulated with blocks: return path from node s0 to y inside SCC via BFS
        static uint8_t cyc1[1 << 20], cyc2[1 << 20]; int l1 = 0, l2 = 0;
        static uint8_t o1[1 << 20], o2[1 << 20]; int m1 = 0, m2 = 0;
        uint64_t rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)qid;
        int have1 = 0, done = 0;
        for (int attempt = 0; attempt < 2000 && !done; attempt++) {
            // random walk from y of length rl inside the SCC, then BFS back to y
            static uint8_t buf[1 << 20]; int bl = 0; uint32_t v = y;
            int rl = 1 + (attempt % 64);
            for (int i = 0; i < rl; i++) {
                uint32_t nb2[2]; int nn = succ(v >> b, v & ((1u << b) - 1), nb2);
                int choices[2], nc = 0;
                for (int c = 0; c < nn; c++) if (comp[nodeid(((v >> b) + 1) % P, nb2[c])] == comp[y]) choices[nc++] = c;
                if (!nc) break;
                rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
                int c = choices[rng % nc]; buf[bl++] = (uint8_t)c; v = nodeid(((v >> b) + 1) % P, nb2[c]);
            }
            // BFS v -> y inside SCC
            int tag = 1000000 + qid * 4096 + attempt; uint32_t qh2 = 0, qt2 = 0; qq[qt2++] = v; mark[v] = tag; par[v] = UINT32_MAX; int found = (v == y && bl > 0);
            while (qh2 < qt2 && !found) {
                uint32_t a = qq[qh2++]; uint32_t nb2[2]; int nn = succ(a >> b, a & ((1u << b) - 1), nb2);
                for (int c = 0; c < nn; c++) { uint32_t u = nodeid(((a >> b) + 1) % P, nb2[c]); if (comp[u] != comp[y]) continue;
                    if (mark[u] != tag) { mark[u] = tag; par[u] = a; pin[u] = (uint8_t)c; qq[qt2++] = u; if (u == y) { found = 1; break; } } }
            }
            if (!found) continue;
            static uint8_t back[1 << 20]; int bkl = 0; if (!(v == y)) { uint32_t a = y; while (a != v) { back[bkl++] = pin[a]; a = par[a]; } }
            static uint8_t cyc[1 << 20]; int cl = 0; for (int i = 0; i < bl; i++) cyc[cl++] = buf[i]; for (int i = bkl - 1; i >= 0; i--) cyc[cl++] = back[i];
            // outputs along the cycle
            static uint8_t oo[1 << 20]; int ol = 0; uint32_t a = y;
            for (int i = 0; i < cl; i++) { if (W[a >> b] == '0') oo[ol++] = (uint8_t)(a & 1); uint32_t nb2[2]; succ(a >> b, a & ((1u << b) - 1), nb2); a = nodeid(((a >> b) + 1) % P, nb2[cyc[i]]); }
            if (a != y) continue;
            if (!have1) { memcpy(cyc1, cyc, cl); l1 = cl; memcpy(o1, oo, ol); m1 = ol; have1 = 1; continue; }
            // test u1 u2 != u2 u1
            int differ = 0; int tot = m1 + ol;
            for (int i = 0; i < tot && !differ; i++) { int x = i < m1 ? o1[i] : oo[i - m1]; int z = i < ol ? oo[i] : o1[i - ol]; if (x != z) differ = 1; }
            if (differ) { memcpy(cyc2, cyc, cl); l2 = cl; memcpy(o2, oo, ol); m2 = ol; done = 1; }
        }
        printf(" cycles ");
        if (!done) { printf("NOTFOUND\n"); continue; }
        for (int i = 0; i < l1; i++) printf("%d", cyc1[i]); printf(" "); for (int i = 0; i < l2; i++) printf("%d", cyc2[i]); printf("\n");
    }
    fclose(g);
    return 0;
}
