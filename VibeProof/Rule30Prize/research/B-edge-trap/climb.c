// Hill-climb over driver prefixes d of length n (= finite right halves of width n) to maximize the lock time
// of column 1 at white phases (driver w^inf after the prefix, phase ph0). S = horizon.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 2048
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
static uint64_t xs = 88172645463325252ULL;
static inline uint64_t rnd(void) { xs ^= xs << 13; xs ^= xs >> 7; xs ^= xs << 17; return xs; }
static int n, ph0; static long S; static uint8_t *col1, *wh;
static Row r;
static long locktime(const uint8_t *d) {
    memset(r.a, 0, sizeof(uint64_t) * 8); r.nw = 1;
    r.a[0] = d[0];
    for (int t = 0; t < n; t++) { step(&r, (t + 1 < n) ? d[t + 1] : (W[ph0] - '0')); }
    for (long s = 0; s <= S; s++) {
        col1[s] = (uint8_t)((r.a[0] >> 1) & 1); wh[s] = (uint8_t)(W[(ph0 + s) % P] == '0');
        if (s < S) step(&r, W[(ph0 + s + 1) % P] - '0');
        if (r.nw >= MAXW - 2) { fprintf(stderr, "overflow\n"); exit(1); }
    }
    long Q = -1;
    for (long q = P; q <= 1024; q += P) {
        int ok = 1;
        for (long s = S / 2; s + q <= S; s++) if (wh[s] && col1[s] != col1[s + q]) { ok = 0; break; }
        if (ok) { Q = q; break; }
    }
    if (Q < 0) return S; // not locked within horizon
    long tau = 0;
    for (long s = S - Q; s >= 0; s--) if (wh[s] && col1[s] != col1[s + Q]) { tau = s + 1; break; }
    return tau;
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); n = atoi(argv[2]); S = atol(argv[3]); ph0 = atoi(argv[4]);
    long iters = atol(argv[5]); xs ^= (uint64_t)atol(argv[6]) * 0x9E3779B97F4A7C15ULL;
    col1 = malloc(S + 1); wh = malloc(S + 1);
    uint8_t *d = malloc(n), *best = malloc(n);
    for (int i = 0; i < n; i++) d[i] = rnd() & 1;
    long bestv = locktime(d); memcpy(best, d, n);
    for (long it = 0; it < iters; it++) {
        memcpy(d, best, n);
        int k = 1 + (int)(rnd() % 3);
        for (int j = 0; j < k; j++) d[rnd() % n] ^= 1;
        long v = locktime(d);
        if (v >= bestv) { if (v > bestv) { } bestv = v; memcpy(best, d, n); }
    }
    printf("w=%s n=%d ph0=%d S=%ld best lock time %ld  d=", W, n, ph0, S, bestv);
    for (int i = 0; i < n; i++) putchar('0' + best[i]);
    printf("\n");
    return 0;
}
