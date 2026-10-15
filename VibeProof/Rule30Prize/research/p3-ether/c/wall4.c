// Wall search for the 12x3 rule-30 ether.
// Attachment column a (ether index mod 12), strip of b cells to its right (bit i = cell a+1+i).
// Node (phi, r), phi in 0..2, r < 2^b.  Successor for right input z: r' = step(E[a][phi], z, r), phi' = phi+1 mod 3.
// U-property: if E[a][phi] == 0 then bit0(r) == E[a+1][phi].
// Reports: bottom SCCs of the all-inputs graph, which of them satisfy U (= minimal walls), smallest wall,
// and the maximal closed U-set (greatest fixed point).  usage: wall3 a b [dumpfile]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static const char *E[12] = {"0011","0110","1101","0101","0011","0001","0001"};
static int b, A; static uint32_t M;
static inline uint32_t stp(int a, int z, uint32_t r) {
    uint64_t full = (uint64_t)a | ((uint64_t)r << 1) | ((uint64_t)z << (b + 1));
    return (uint32_t)((full ^ ((full >> 1) | (full >> 2))) & (uint64_t)(M - 1));
}
static inline uint32_t succ(uint32_t v, int z) {
    int phi = v / M; uint32_t r = v % M; int a = E[A][phi] - '0';
    return (uint32_t)(((phi + 1) % 4) * M + stp(a, z, r));
}
static inline int uok(uint32_t v) {
    int phi = v / M; uint32_t r = v % M;
    if (E[A][phi] == '1') return 1;
    return (int)(r & 1) == (E[(A + 1) % 7][phi] - '0');
}
int main(int argc, char **argv) {
    A = atoi(argv[1]); b = atoi(argv[2]); M = 1u << b; uint32_t N = 4 * M;
    FILE *dump = argc > 3 ? fopen(argv[3], "w") : NULL;
    // greatest closed U-set
    uint8_t *in = malloc(N); long cnt = 0;
    for (uint32_t v = 0; v < N; v++) { in[v] = (uint8_t)uok(v); cnt += in[v]; }
    int changed = 1;
    while (changed) { changed = 0;
        for (uint32_t v = 0; v < N; v++) if (in[v] && (!in[succ(v, 0)] || !in[succ(v, 1)])) { in[v] = 0; cnt--; changed = 1; } }
    // Tarjan SCC (iterative)
    int32_t *idx = malloc(4 * (size_t)N), *low = malloc(4 * (size_t)N), *comp = malloc(4 * (size_t)N);
    uint8_t *onst = calloc(N, 1); uint32_t *stk = malloc(4 * (size_t)N), *cs = malloc(4 * (size_t)N); uint8_t *ci = malloc(N);
    for (uint32_t i = 0; i < N; i++) idx[i] = -1;
    int32_t counter = 0, nc = 0; uint32_t sp = 0;
    for (uint32_t root = 0; root < N; root++) {
        if (idx[root] != -1) continue;
        uint32_t csp = 0; cs[csp] = root; ci[csp] = 0; csp++;
        while (csp) {
            uint32_t v = cs[csp - 1]; int i = ci[csp - 1];
            if (i == 0) { idx[v] = low[v] = counter++; stk[sp++] = v; onst[v] = 1; }
            int pushed = 0;
            while (i < 2) {
                uint32_t u = succ(v, i); i++;
                if (idx[u] == -1) { ci[csp - 1] = (uint8_t)i; cs[csp] = u; ci[csp] = 0; csp++; pushed = 1; break; }
                else if (onst[u] && idx[u] < low[v]) low[v] = idx[u];
            }
            if (pushed) continue;
            ci[csp - 1] = (uint8_t)i;
            if (low[v] == idx[v]) { uint32_t u; do { u = stk[--sp]; onst[u] = 0; comp[u] = nc; } while (u != v); nc++; }
            csp--;
            if (csp) { uint32_t pv = cs[csp - 1]; if (low[v] < low[pv]) low[pv] = low[v]; }
        }
    }
    int32_t *csz = calloc(nc, 4); uint8_t *bottom = malloc(nc), *uall = malloc(nc);
    memset(bottom, 1, nc); memset(uall, 1, nc);
    for (uint32_t v = 0; v < N; v++) { csz[comp[v]]++; if (!uok(v)) uall[comp[v]] = 0;
        for (int z = 0; z < 2; z++) if (comp[succ(v, z)] != comp[v]) bottom[comp[v]] = 0; }
    int nb = 0, nw = 0, best = -1; long wallunion = 0;
    for (int c = 0; c < nc; c++) if (bottom[c]) { nb++; if (uall[c]) { nw++; wallunion += csz[c]; if (best < 0 || csz[c] < csz[best]) best = c; } }
    printf("a=%d (%s|%s) b=%d: maximal closed U-set %ld; bottom SCCs %d (sizes:", A, E[A], E[(A+1)%12], b, cnt, nb);
    int shown = 0; for (int c = 0; c < nc && shown < 12; c++) if (bottom[c]) { printf(" %d%s", csz[c], uall[c] ? "U" : ""); shown++; }
    if (nb > shown) printf(" ...");
    printf("); U-walls %d (union %ld)", nw, wallunion);
    if (best >= 0) {
        long per[4] = {0}; for (uint32_t v = 0; v < N; v++) if (comp[v] == best) per[v / M]++;
        printf(" smallest wall %d states (per phase %ld %ld %ld)", csz[best], per[0], per[1], per[2]);
        if (dump) { for (uint32_t v = 0; v < N; v++) if (comp[v] == best) fprintf(dump, "%u %u\n", v / M, v % M); }
    }
    printf("\n");
    if (dump) fclose(dump);
    return 0;
}
