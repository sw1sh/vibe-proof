// Weak right-absorption statistics: right half driven by w^inf from random finite initial states.
// Reports fraction of trials where col_1 restricted to zeros of c is periodic on the second half
// (period multiple of P up to 64P), plus whether full col_1 is periodic.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXT 20000
#define NW 512
static uint64_t row[NW], nrow[NW];
static unsigned char col1[MAXT];
static uint64_t rs = 88172645463325252ULL;
static uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    const char *w = argv[1]; int P = strlen(w);
    int steps = atoi(argv[2]); int trials = atoi(argv[3]); int initw = atoi(argv[4]);
    if (argc > 5) rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    int nw = (initw + steps + 64) / 64 + 1; if (nw > NW) { fprintf(stderr, "too wide\n"); return 1; }
    int nabs = 0, nfull = 0; long sumT = 0; int maxT = 0;
    for (int tr = 0; tr < trials; tr++) {
        memset(row, 0, sizeof(uint64_t) * nw);
        for (int i = 0; i < initw; i++) if (xr() & 1) row[i >> 6] |= 1ULL << (i & 63);
        // bit i <-> position i+1
        for (int t = 0; t < steps; t++) {
            int ct = w[t % P] - '0';
            col1[t] = row[0] & 1;
            for (int k = 0; k < nw; k++) {
                uint64_t leftn = (row[k] << 1) | (k ? row[k - 1] >> 63 : (uint64_t)ct);
                uint64_t rightn = (row[k] >> 1) | (k + 1 < nw ? row[k + 1] << 63 : 0);
                nrow[k] = leftn ^ (row[k] | rightn);
            }
            memcpy(row, nrow, sizeof(uint64_t) * nw);
        }
        int start = steps / 2, found = 0, foundfull = 0, Tabs = -1;
        for (int m = 1; m <= 64 && !found; m++) {
            int Q = P * m; if (start + Q >= steps) break;
            int ok = 1;
            for (int t = start; t + Q < steps; t++) if (w[t % P] == '0' && col1[t] != col1[t + Q]) { ok = 0; break; }
            if (ok) {
                found = 1;
                int T = start; while (T > 0 && (w[(T - 1) % P] == '1' || col1[T - 1] == col1[T - 1 + Q])) T--;
                Tabs = T;
                int okf = 1; for (int t = start; t + Q < steps; t++) if (col1[t] != col1[t + Q]) { okf = 0; break; }
                foundfull = okf;
            }
        }
        if (found) { nabs++; sumT += Tabs; if (Tabs > maxT) maxT = Tabs; }
        if (foundfull) nfull++;
    }
    printf("%s P=%d: absorbed %d/%d (full col1 periodic %d), mean T %.0f max T %d\n", w, P, nabs, trials, nfull, nabs ? (double)sumT / nabs : -1.0, maxT);
    return 0;
}
