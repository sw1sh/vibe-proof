// Search for finite right states (driven by w^inf) with long absorption times.
// Absorption = strip [1..b] enters a certified trap (read from file) at the matching phase.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NW 160
static uint64_t row[NW], nrow[NW];
static int P, b; static const char *W;
static uint8_t *intrap[64];  // intrap[phase][state]
static uint8_t col1h[20000];
static uint64_t rs = 0x123456789ULL;
static uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int run(int maxT, int nw) {
    for (int t = 0; t < maxT; t++) {
        int ph = t % P;
        col1h[t] = row[0] & 1;
        uint32_t s = (uint32_t)(row[0] & ((1ULL << b) - 1));
        if (intrap[ph][s] && !getenv("NOTRAP")) return t;
        int ct = W[ph] - '0';
        for (int k = 0; k < nw; k++) {
            uint64_t leftn = (row[k] << 1) | (k ? row[k - 1] >> 63 : (uint64_t)ct);
            uint64_t rightn = (row[k] >> 1) | (k + 1 < nw ? row[k + 1] << 63 : 0);
            nrow[k] = leftn ^ (row[k] | rightn);
        }
        memcpy(row, nrow, sizeof(uint64_t) * nw);
    }
    return -1;
}
int main(int argc, char **argv) {
    const char *trapfile = argv[1]; int maxT = atoi(argv[2]); int trials = atoi(argv[3]); int width = atoi(argv[4]);
    FILE *f = fopen(trapfile, "r"); char wbuf[64]; int n;
    if (fscanf(f, "%63s %d %d", wbuf, &b, &n) != 3) return 1;
    W = strdup(wbuf); P = strlen(W);
    for (int p = 0; p < P; p++) intrap[p] = calloc(1u << b, 1);
    for (int i = 0; i < n; i++) { int ph; unsigned s; int pos; if (fscanf(f, "%d %u %d", &ph, &s, &pos) != 3) return 1; intrap[ph][s] = 1; }
    fclose(f);
    int nw = (width + maxT) / 64 + 2; if (nw > NW) nw = NW;
    int worst = 0, never = 0, otherabs = 0; long sum = 0; int hist[12] = {0};
    for (int tr = 0; tr < trials; tr++) {
        memset(row, 0, sizeof row);
        int mode = tr % 6;
        int wd = 1 + (int)(xr() % width);
        int per = 1 + (int)(xr() % 12); uint64_t pat = xr();
        double dens = (xr() % 1000) / 1000.0;
        for (int i = 0; i < wd; i++) {
            int v;
            if (mode == 0) v = xr() & 1;
            else if (mode == 1) v = ((xr() % 1000) / 1000.0) < dens;
            else if (mode == 2) v = (pat >> (i % per)) & 1;
            else if (mode == 3) v = (i % per == 0);
            else if (mode == 4) v = (pat >> (i % per)) & 1 ^ (((xr() % 100) < 3) ? 1 : 0);
            else v = (i < wd / 2) ? (xr() & 1) : ((pat >> (i % per)) & 1);
            if (v) row[i >> 6] |= 1ULL << (i & 63);
        }
        // random starting phase: rotate driver by burning steps with phase offset -> emulate by initial phase shift
        int r = run(maxT, nw);
        if (r < 0) {
            // masked periodicity test on second half
            int start = maxT / 2, found = 0;
            for (int m = 1; m <= 64 && !found; m++) { int Q = P * m; if (start + Q >= maxT) break; int ok = 1;
                for (int t = start; t + Q < maxT; t++) if (W[t % P] == '0' && col1h[t] != col1h[t + Q]) { ok = 0; break; }
                if (ok) found = 1; }
            if (found) otherabs++; else { never++; if (never <= 3) { printf("  non-absorbed example mode=%d width=%d\n", mode, wd); } }
        } else { sum += r; if (r > worst) worst = r; int bin = 0; int x = r; while (x > 1 && bin < 11) { x >>= 1; bin++; } hist[bin]++; }
    }
    printf("other-absorbed=%d ", otherabs); printf("%s b=%d trap=%d: trials=%d never(<%d)=%d worst=%d mean=%.1f  log2-hist:", W, b, n, trials, maxT, never, worst, (trials - never) ? (double)sum / (trials - never) : -1.0);
    for (int i = 0; i < 12; i++) printf(" %d", hist[i]);
    printf("\n");
    return 0;
}
