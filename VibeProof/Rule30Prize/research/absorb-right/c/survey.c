// Survey: for each word given on stdin (one per line), run all phases x configs, report periodicity of column 1.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static u64 rng_s;
static u64 rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static void step(u64 *row, int nw, int c) {
    u64 carry = (u64)c;
    for (int j = 0; j < nw; j++) {
        u64 cur = row[j]; u64 nxt = (j + 1 < nw) ? row[j + 1] : 0;
        u64 left = (cur << 1) | carry, right = (cur >> 1) | (nxt << 63);
        carry = cur >> 63; row[j] = left ^ (cur | right);
    }
}
static int smallest_period(const uint8_t *s, int n, int *f) {
    f[0] = -1; int k = -1;
    for (int i = 0; i < n; i++) { while (k >= 0 && s[k] != s[i]) k = f[k]; k++; f[i + 1] = k; }
    return n - f[n];
}
static u64 *realrow[8]; static long realW[8] = {50, 200, 700, 1500, 3000, 0, 0, 0}; static int nreal = 5;
static void make_real(long W, u64 *out) {
    long L = 2 * W + 3; int nw2 = (int)(L / 64 + 2); u64 *r = calloc(nw2, 8), *t2 = calloc(nw2, 8);
    long off = W + 1; r[off / 64] |= 1ULL << (off % 64);
    for (long t = 0; t < W; t++) {
        for (int j = 0; j < nw2; j++) { u64 cur = r[j], prv = j ? r[j - 1] : 0, nx = (j + 1 < nw2) ? r[j + 1] : 0;
            t2[j] = ((cur << 1) | (prv >> 63)) ^ (cur | ((cur >> 1) | (nx << 63))); }
        memcpy(r, t2, nw2 * 8);
    }
    for (long p = 1; p <= W; p++) { long b = p + off; if ((r[b / 64] >> (b % 64)) & 1) out[(p - 1) / 64] |= 1ULL << ((p - 1) % 64); }
    free(r); free(t2);
}
int main(int argc, char **argv) {
    long N = atol(argv[1]); int nrand = atoi(argv[2]); long maxW = atol(argv[3]);
    long width = maxW + 3000 + N + 128; int nw = (int)(width / 64 + 2);
    for (int i = 0; i < nreal; i++) { realrow[i] = calloc(nw, 8); make_real(realW[i], realrow[i]); }
    u64 *row = malloc(nw * 8); uint8_t *col = malloc(N); int *f = malloc(sizeof(int) * (N + 2));
    char w[128];
    while (scanf("%127s", w) == 1) {
        int P = strlen(w); int wb[128]; for (int i = 0; i < P; i++) wb[i] = w[i] - '0';
        int nper = 0, ntot = 0; long maxT = 0; int periods[64]; int np = 0; int aper_example = -1;
        for (int ph = 0; ph < P; ph++) {
            for (int cfg = 0; cfg < nreal + nrand + 1; cfg++) {
                memset(row, 0, nw * 8);
                if (cfg < nreal) memcpy(row, realrow[cfg], nw * 8);
                else if (cfg < nreal + nrand) {
                    rng_s = (u64)(cfg * 1000003 + ph * 7919 + 12345) * 2654435761ULL + 88172645463325252ULL; for (int i = 0; i < 10; i++) rnd();
                    long W = (cfg - nreal) % 3 == 0 ? 20 : ((cfg - nreal) % 3 == 1 ? maxW / 10 : maxW);
                    for (long i = 0; i < W; i++) if (rnd() & 1) row[i / 64] |= 1ULL << (i % 64);
                } // else zero config
                for (long t = 0; t < N; t++) {
                    col[t] = row[0] & 1;
                    long need = (N - t) + 2; int nwa = (int)(need / 64 + 2); if (nwa > nw) nwa = nw;
                    step(row, nwa, wb[(ph + t) % P]);
                }
                long h = N / 2; int p = smallest_period(col + h, (int)(N - h), f);
                ntot++;
                if (p <= (N - h) / 3) {
                    long T = h; while (T > 0 && col[T - 1] == col[T - 1 + p]) T--;
                    nper++; if (T > maxT) maxT = T;
                    int seen = 0; for (int i = 0; i < np; i++) if (periods[i] == p) seen = 1;
                    if (!seen && np < 64) periods[np++] = p;
                } else if (aper_example < 0) aper_example = ph * 100 + cfg;
            }
        }
        printf("%-12s %3d/%3d periodic", w, nper, ntot);
        if (np) { printf(" periods:"); for (int i = 0; i < np; i++) printf(" %d", periods[i]); printf(" maxT %ld", maxT); }
        printf("\n"); fflush(stdout);
    }
    return 0;
}
