// Adversarial hill-climbing: find initial right-half configs (width W) that delay periodicity of column 1.
// Score = transient T (start of eventual periodicity of column 1 within N steps), or N if aperiodic.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static u64 rng_s = 88172645463325252ULL;
static u64 rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static int P; static int wb[128]; static long N; static int nw;
static u64 *row; static uint8_t *col; static int *f;
static void step(u64 *r, int n, int c) {
    u64 carry = (u64)c;
    for (int j = 0; j < n; j++) { u64 cur = r[j], nxt = (j + 1 < n) ? r[j + 1] : 0;
        u64 left = (cur << 1) | carry, right = (cur >> 1) | (nxt << 63); carry = cur >> 63; r[j] = left ^ (cur | right); }
}
static long score(const u64 *init, int ph) {
    memcpy(row, init, nw * 8);
    for (long t = 0; t < N; t++) { col[t] = row[0] & 1; long need = (N - t) + 2; int nwa = (int)(need / 64 + 2); if (nwa > nw) nwa = nw; step(row, nwa, wb[(ph + t) % P]); }
    // eventual period from the end: find smallest p <= maxp such that col[t]==col[t+p] on last quarter; then T
    long q = N / 4; int best = -1;
    for (int p = 1; p <= 64 && best < 0; p++) { int ok = 1; for (long t = N - q; t + p < N; t++) if (col[t] != col[t + p]) { ok = 0; break; } if (ok) best = p; }
    if (best < 0) return N;
    long T = N - q; while (T > 0 && col[T - 1] == col[T - 1 + best]) T--;
    return T;
}
int main(int argc, char **argv) {
    const char *w = argv[1]; long W = atol(argv[2]); N = atol(argv[3]); long iters = atol(argv[4]); rng_s ^= atol(argv[5]) * 0x9E3779B97F4A7C15ULL;
    int ph = argc > 6 ? atoi(argv[6]) : 0;
    P = strlen(w); for (int i = 0; i < P; i++) wb[i] = w[i] - '0';
    nw = (int)((W + N + 128) / 64 + 2);
    row = calloc(nw, 8); col = malloc(N); f = malloc(sizeof(int) * (N + 2));
    u64 *cur = calloc(nw, 8), *cand = calloc(nw, 8);
    for (long i = 0; i < W; i++) if (rnd() & 1) cur[i / 64] |= 1ULL << (i % 64);
    long sc = score(cur, ph), best = sc;
    for (long it = 0; it < iters; it++) {
        memcpy(cand, cur, nw * 8);
        int nflip = 1 + (rnd() % 3);
        for (int k = 0; k < nflip; k++) { long i = rnd() % W; cand[i / 64] ^= 1ULL << (i % 64); }
        long s2 = score(cand, ph);
        if (s2 >= sc) { memcpy(cur, cand, nw * 8); sc = s2; if (sc > best) { best = sc; } }
    }
    printf("%s W=%ld N=%ld: best transient %ld\n", w, W, N, best);
    // print config prefix
    printf("config: "); for (long i = 0; i < W && i < 200; i++) putchar(((cur[i / 64] >> (i % 64)) & 1) ? '1' : '0'); printf("\n");
    return 0;
}
