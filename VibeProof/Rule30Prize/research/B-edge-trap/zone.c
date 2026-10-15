// For driven right halves (empty start, driver prefix d of length n, then w^inf from phase ph0):
// simulate S steps, then over the window [S/2, S) find, for periods p in {P, 2P, 4P, ..., 2^k P},
// the width of the zone of columns 1..K that are p-periodic; and whether column 1 at white phases is p-periodic.
// Modes: zone w n S [random count seed width] ; prints histogram of zone widths and number of col1-white-aperiodic runs.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 8192
static int P; static const char *W;
typedef struct { uint64_t a[MAXW]; int nw; } Row;
static inline void step(Row *r, int c) {
    int nw = r->nw;
    if ((r->a[nw - 1] >> 62) != 0) { r->a[nw] = 0; nw = ++r->nw; }
    uint64_t prev_hi = 0;
    for (int i = 0; i < nw; i++) {
        uint64_t x = r->a[i];
        uint64_t left = (x << 1) | prev_hi;
        uint64_t nxt = (i + 1 < nw) ? r->a[i + 1] : 0;
        uint64_t right = (x >> 1) | (nxt << 63);
        prev_hi = x >> 63;
        r->a[i] = left ^ (x | right);
    }
    r->a[0] = (r->a[0] & ~1ULL) | (uint64_t)c;
}
static uint64_t *hist_rows; // columns 1..64 at each time in window
static uint64_t xs = 88172645463325252ULL;
static inline uint64_t rnd(void) { xs ^= xs << 13; xs ^= xs >> 7; xs ^= xs << 17; return xs; }
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); int n = atoi(argv[2]); long S = atol(argv[3]);
    int random_mode = argc > 4 && strcmp(argv[4], "true"); long count = random_mode ? atol(argv[4]) : 0; if (random_mode) xs ^= (uint64_t)atol(argv[5]) * 0x9E3779B97F4A7C15ULL;
    int true_mode = argc > 4 && !strcmp(argv[4], "true"); long Ta = 0, Tb = 0, Ts = 1;
    static uint8_t cbits[1250000];
    if (true_mode) { sscanf(argv[5], "%ld:%ld:%ld", &Ta, &Tb, &Ts); FILE *cf = fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", "rb"); if (fread(cbits, 1, 1250000, cf) != 1250000) return 1; fclose(cf); }
    long half = S / 2; long WL = S - half;
    hist_rows = malloc(sizeof(uint64_t) * WL);
    static Row r;
    long zh[70] = {0}; long nap = 0, total = 0;
    long nruns = random_mode ? count : true_mode ? (Tb - Ta) / Ts + 1 : (1L << n);
    static uint64_t d[4096]; // up to 262144 prefix bits
    for (long id = 0; id < nruns; id++) {
        int nn = n;
        if (random_mode) { for (int i = 0; i < (nn + 63) / 64; i++) d[i] = rnd(); }
        else if (true_mode) { nn = (int)(Ta + id * Ts); memset(d, 0, sizeof d); for (int i = 0; i < nn; i++) if ((cbits[i >> 3] >> (7 - (i & 7))) & 1) d[i >> 6] |= 1ULL << (i & 63); }
        else d[0] = (uint64_t)id;
        for (int ph0 = 0; ph0 < P; ph0++) {
            memset(&r, 0, sizeof r); r.nw = 1;
            #define DB(t) ((int)((d[(t) >> 6] >> ((t) & 63)) & 1))
            r.a[0] = nn > 0 ? (uint64_t)DB(0) : (uint64_t)(W[ph0] - '0');
            long t = 0;
            for (; t < nn + S; t++) {
                if (t >= nn + half) hist_rows[t - nn - half] = (r.a[0] >> 1) | (r.nw > 1 ? (r.a[1] << 63) : 0);
                long t1 = t + 1;
                int c1 = (t1 < nn) ? DB(t1) : (W[(ph0 + (t1 - nn)) % P] - '0');
                step(&r, c1);
                if (r.nw >= MAXW - 2) { fprintf(stderr, "overflow\n"); return 1; }
            }
            // analyze window: times nn+half .. nn+S-1, phase of time t is (ph0 + t - nn) % P
            int bestK = 0; int col1ok = 0;
            for (long p = P; p <= 256 * P && p < WL / 2; p *= 2) {
                uint64_t diff = 0, diffw = 0;
                for (long i = 0; i + p < WL; i++) {
                    uint64_t x = hist_rows[i] ^ hist_rows[i + p];
                    diff |= x;
                    int ph = (int)((ph0 + half + i) % P);
                    if (W[ph] == '0') diffw |= x & 1;
                }
                int K = diff ? __builtin_ctzll(diff) : 64;
                if (K > bestK) bestK = K;
                if (!diffw) col1ok = 1;
            }
            zh[bestK]++; total++;
            if (getenv("SHOWZ") && bestK >= atoi(getenv("SHOWZ")) && zh[bestK] <= 3) printf("zone %d: id=%ld nn=%d ph0=%d\n", bestK, id, nn, ph0);
            if (!col1ok) { nap++; if (nap <= 10) printf("col1-white aperiodic: id=%ld nn=%d ph0=%d\n", id, nn, ph0); }
        }
    }
    printf("w=%s n=%d S=%ld runs=%ld col1-white-aperiodic=%ld zone-width hist:", W, n, S, total, nap);
    for (int k = 0; k <= 64; k++) if (zh[k]) printf(" %d:%ld", k, zh[k]);
    printf("\n");
    return 0;
}
