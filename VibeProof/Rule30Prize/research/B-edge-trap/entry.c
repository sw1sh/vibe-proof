// Driven right half of rule 30: columns 0..L, column 0 = driver.  new[p] = old[p-1] ^ (old[p] | old[p+1]), p >= 1.
// Start: empty right half, driver d_0..d_{n-1} (all 2^n words, or given), then w^inf starting at phase ph0.
// Entry time = first t >= n (or >= start) with SAFE[(phase(t), strip(t))].
// Modes:
//   entry w b safefile prefix n maxsteps        : all prefixes of length n, all phases
//   entry w b safefile true Tlist maxsteps      : true center prefix c(0..T-1) for T in list (comma separated or a:b:step)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 1024
typedef struct { uint64_t a[MAXW]; int nw; } Row;
static int P, b; static const char *W; static uint8_t *SAFE;
static inline void step(Row *r, int c) {
    // compute new row; bit p of word p>>6
    int nw = r->nw;
    // ensure room for growth by one bit
    if ((r->a[nw - 1] >> 62) != 0) { r->a[nw] = 0; nw = ++r->nw; }
    uint64_t carry_in = (uint64_t)c; // old[-1] -> for p=0 we overwrite
    uint64_t prev_hi = 0;
    for (int i = 0; i < nw; i++) {
        uint64_t x = r->a[i];
        uint64_t left = (x << 1) | prev_hi;         // old[p-1] at bit p
        uint64_t nxt = (i + 1 < nw) ? r->a[i + 1] : 0;
        uint64_t right = (x >> 1) | (nxt << 63);   // old[p+1] at bit p
        prev_hi = x >> 63;
        r->a[i] = left ^ (x | right);
    }
    (void)carry_in;
    r->a[0] = (r->a[0] & ~1ULL) | (uint64_t)c; // column 0 = driver at the new time (set by caller later)
}
static inline uint32_t strip(const Row *r) { return (uint32_t)((r->a[0] >> 1) & ((1ULL << b) - 1)); }
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage\n"); return 1; }
    W = argv[1]; P = strlen(W); b = atoi(argv[2]);
    FILE *f = fopen(argv[3], "rb"); uint32_t N = (uint32_t)P << b; SAFE = malloc(N);
    if (fread(SAFE, 1, N, f) != N) { fprintf(stderr, "bad safe file\n"); return 1; } fclose(f);
    const char *mode = argv[4]; long maxsteps = atol(argv[6]);
    if (!strcmp(mode, "prefix")) {
        int n = atoi(argv[5]);
        long hist[64] = {0}; long maxt = -1; long nfail = 0; long total = 0;
        static Row r;
        for (uint32_t d = 0; d < (1u << n); d++) {
            for (int ph0 = 0; ph0 < P; ph0++) {
                memset(&r, 0, sizeof r); r.nw = 1;
                // time 0: column 0 = d_0
                int c0 = n > 0 ? (d & 1) : (W[ph0] - '0');
                r.a[0] = (uint64_t)c0;
                long t = 0; long entry = -1;
                for (;;) {
                    // at time t, column 0 already set to c(t)
                    if (t >= n) {
                        int ph = (int)((ph0 + (t - n)) % P);
                        if (SAFE[((uint32_t)ph << b) | strip(&r)]) { entry = t - n; break; }
                    }
                    if (t - n >= maxsteps) break;
                    long t1 = t + 1;
                    int c1 = (t1 < n) ? (int)((d >> t1) & 1) : (W[(ph0 + (t1 - n)) % P] - '0');
                    step(&r, c1);
                    if (r.nw >= MAXW - 2) { fprintf(stderr, "width overflow\n"); return 1; }
                    t = t1;
                }
                total++;
                if (entry < 0) { nfail++; if (nfail <= 5) printf("NO ENTRY within %ld: d=%u ph0=%d\n", maxsteps, d, ph0); }
                else { if (entry > maxt) maxt = entry; int bk = 0; long e = entry; while (e) { bk++; e >>= 1; } hist[bk]++; }
            }
        }
        printf("w=%s b=%d n=%d runs=%ld fails=%ld max entry delay=%ld  log2-hist:", W, b, n, total, nfail, maxt);
        for (int i = 0; i < 40; i++) if (hist[i]) printf(" [%d]%ld", i, hist[i]);
        printf("\n");
    } else if (!strcmp(mode, "true")) {
        // true center column computed on the fly; parse T range a:b:step
        long Ta, Tb, Ts; if (sscanf(argv[5], "%ld:%ld:%ld", &Ta, &Tb, &Ts) != 3) { fprintf(stderr, "range a:b:step\n"); return 1; }
        static Row full; // full right half of the true pattern, driven by true c; we also need true c: compute full pattern
        // true pattern: full row over p in [-t, t]; store as offset array
        int FW = (int)((2 * Tb + 200) / 64 + 2);
        uint64_t *row = calloc(FW, 8), *nrow = calloc(FW, 8);
        long off = Tb + 64; // position p stored at bit (p + off)
        row[off >> 6] |= 1ULL << (off & 63);
        long t = 0;
        static Row r;
        long maxdelay = -1;
        for (long T = Ta; T <= Tb; T += Ts) {
            while (t < T) {
                for (int i = 0; i < FW; i++) {
                    uint64_t x = row[i];
                    uint64_t lo = i ? row[i - 1] >> 63 : 0;
                    uint64_t hi = (i + 1 < FW) ? row[i + 1] << 63 : 0;
                    uint64_t left = (x << 1) | lo, right = (x >> 1) | hi;
                    nrow[i] = left ^ (x | right);
                }
                uint64_t *tmp = row; row = nrow; nrow = tmp; t++;
            }
            for (int ph0 = 0; ph0 < P; ph0++) {
                // right half at time T: columns 0..T from the true row, then replace c(T) by w[ph0]
                memset(&r, 0, sizeof r);
                long ncol = T + 2; r.nw = (int)(ncol / 64 + 2);
                if (r.nw >= MAXW - 2) { fprintf(stderr, "T too large\n"); return 1; }
                for (long p = 0; p <= T; p++) { long q = p + off; if ((row[q >> 6] >> (q & 63)) & 1) r.a[p >> 6] |= 1ULL << (p & 63); }
                r.a[0] = (r.a[0] & ~1ULL) | (uint64_t)(W[ph0] - '0');
                long s = 0; long entry = -1;
                for (;;) {
                    int ph = (int)((ph0 + s) % P);
                    if (SAFE[((uint32_t)ph << b) | strip(&r)]) { entry = s; break; }
                    if (s >= maxsteps) break;
                    s++;
                    step(&r, W[(ph0 + s) % P] - '0');
                    if (r.nw >= MAXW - 2) { fprintf(stderr, "width overflow\n"); return 1; }
                }
                if (entry > maxdelay) maxdelay = entry;
                printf("T=%ld ph0=%d entry delay=%ld\n", T, ph0, entry);
            }
        }
        printf("max delay %ld\n", maxdelay);
    }
    return 0;
}
