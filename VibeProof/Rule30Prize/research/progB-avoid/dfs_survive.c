// Construct a finitely supported right half whose width-b strip stays in the bad SCC B_b for L steps,
// by DFS over the initial cells (column b+t at time 0 is chosen at step t; the strip at time t depends only
// on columns 1..b+t at time 0). Then continue the free evolution (zeros beyond b+L) and report when the strip
// leaves B_b. B_b is read from a dump file "phase state comp" (unique bad SCC).
// usage: dfs_survive w b dumpfile L seed
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static const char *W; static int P, b, L;
static uint8_t *inB;
#define MAXL 4096
static uint8_t tri[MAXL + 64][MAXL + 128]; // tri[s][p] = cell at time s, column p (1-based), p <= b + L - s
static uint8_t init_[MAXL + 128];
static uint64_t rng = 0x9E3779B97F4A7C15ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static int ph0;
static inline int cval(int s) { return W[(ph0 + s) % P] - '0'; }
static long nodes;
// extend anti-diagonal for new initial column m = b + t: compute tri[s][m - s] for s = 1..t
static void computeAD(int m) {
    tri[0][m] = init_[m];
    for (int s = 1; s < m; s++) {
        int p = m - s;
        int left = (p - 1 == 0) ? cval(s - 1) : tri[s - 1][p - 1];
        tri[s][p] = left ^ (tri[s - 1][p] | tri[s - 1][p + 1]);
    }
}
static void extend(int t) { computeAD(b + t); }
static uint32_t stripAt(int s) { uint32_t v = 0; for (int p = 1; p <= b; p++) v |= (uint32_t)tri[s][p] << (p - 1); return v; }
static int found = 0;
// randomized local search: assign bits forward; on failure at time t, jump back K steps and resample
static int search(void) {
    int t = 1; long fails = 0;
    while (t <= L) {
        nodes++;
        init_[b + t] = (uint8_t)(xr() & 1);
        extend(t);
        uint32_t v = ((uint32_t)((ph0 + t) % P) << b) | stripAt(t);
        if (inB[v]) { t++; continue; }
        fails++;
        int K = 1 + (int)(xr() % (t < 8 ? 8 : t));
        t = t - K; if (t < 1) t = 1;
        // recompute anti-diagonals b+1 .. b+t-1 are still valid (they only depend on bits <= b+t-1)
        if (nodes > 20000000L) { fprintf(stderr, "giving up; fails %ld\n", fails); return 0; }
        { static int maxt = 0; if (t > maxt) { maxt = t; } if ((nodes & 0xFFFFF) == 0) fprintf(stderr, "nodes %ld t %d maxt %d\n", nodes, t, maxt); }
    }
    found = 1; return 1;
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); b = atoi(argv[2]); const char *fn = argv[3]; L = atoi(argv[4]);
    rng ^= (uint64_t)atol(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 20; i++) xr();
    uint32_t N = (uint32_t)P << b; inB = calloc(N, 1);
    FILE *f = fopen(fn, "r"); unsigned ph, s; int c; long nb = 0;
    while (fscanf(f, "%u %u %d", &ph, &s, &c) == 3) { inB[(ph << b) | s] = 1; nb++; }
    fclose(f);
    // initial strip (columns 1..b at time 0): random member of B_b
    uint32_t start; do { start = (uint32_t)(xr() % N); } while (!inB[start]);
    ph0 = start >> b; for (int p = 1; p <= b; p++) init_[p] = (start >> (p - 1)) & 1;
    for (int d = 1; d <= b; d++) computeAD(d);
    // need tri for s >= 1 for columns 1..b: they get filled by extend as t grows (anti-diagonals)
    // at t = 0 the strip is the initial strip: fine. extend(t) for t>=1 fills tri[s][b+t-s].
    // but tri[s][p] for p < b at small s requires columns up to p + s <= b + t: filled when t >= p + s - b.
    // For s >= 1 and p <= b, p + s - b <= s, so by the time we check strip at time t all needed are filled.
    int ok = search();
    printf("w=%s b=%d |B|=%ld L=%d: %s (dfs nodes %ld), phase0=%d\n", W, b, nb, L, ok ? "found config" : "not found", nodes, ph0);
    if (!ok) return 0;
    { char fnm[256]; snprintf(fnm, sizeof fnm, "surv_cfg_%s_%d_%d.txt", W, L, (int)(argc > 5 ? atoi(argv[5]) : 0));
      FILE *g = fopen(fnm, "w"); fprintf(g, "%d ", ph0); for (int p = 1; p <= b + L; p++) fputc('0' + init_[p], g); fputc('\n', g); fclose(g); }
    // free continuation with zeros beyond b+L: simulate full rows
    int n = b + L;
    static uint8_t row[2 * MAXL + 256], nr[2 * MAXL + 256];
    memset(row, 0, sizeof(row));
    for (int p = 1; p <= n; p++) row[p] = init_[p];
    int leave = -1; int width = n + 1;
    for (int t = 0; t < L + 6000 && width < 2 * MAXL + 200; t++) {
        uint32_t v = ((uint32_t)((ph0 + t) % P) << b); for (int p = 1; p <= b; p++) v |= (uint32_t)row[p] << (p - 1);
        if (!inB[v]) { leave = t; break; }
        row[0] = (uint8_t)cval(t);
        for (int p = 1; p <= width; p++) nr[p] = row[p - 1] ^ (row[p] | row[p + 1]);
        width++;
        for (int p = 1; p <= width; p++) row[p] = nr[p];
    }
    printf("  support %d; strip stays in B_b until t = %d (%s); excess beyond support-b: %d\n", n, leave, leave < 0 ? "never within horizon" : "left", leave < 0 ? -1 : leave - L);
    return 0;
}
