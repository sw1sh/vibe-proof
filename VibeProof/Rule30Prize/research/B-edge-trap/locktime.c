// For all driver prefixes d of length n (= all finite right halves with support in [1,n]) and all phases:
// simulate S steps after the prefix; find the final period Q (multiple of P, <= 1024) of column 1 at white phases
// over [S/2, S), and the lock time tau = first s >= 0 (steps after the prefix) from which column 1 at white phases
// agrees with its Q-periodic continuation up to S. Report max tau and the argmax.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 1024
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
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); int n = atoi(argv[2]); long S = atol(argv[3]);
    uint32_t dlo = argc > 4 ? (uint32_t)atol(argv[4]) : 0, dhi = argc > 5 ? (uint32_t)atol(argv[5]) : (1u << n);
    uint8_t *col1 = malloc(S + 1); uint8_t *wh = malloc(S + 1);
    static Row r;
    long maxtau = -1; uint32_t argd = 0; int argph = 0; long naper = 0;
    long tauhist[32] = {0};
    for (uint32_t d = dlo; d < dhi; d++) {
        for (int ph0 = 0; ph0 < P; ph0++) {
            memset(r.a, 0, sizeof(uint64_t) * 8); r.nw = 1;
            r.a[0] = n > 0 ? (d & 1) : (uint64_t)(W[ph0] - '0');
            for (int t = 0; t < n; t++) step(&r, (t + 1 < n) ? (int)((d >> (t + 1)) & 1) : (W[ph0] - '0'));
            // now at time n, column 0 = w[ph0]
            for (long s = 0; s <= S; s++) {
                col1[s] = (uint8_t)((r.a[0] >> 1) & 1); wh[s] = (uint8_t)(W[(ph0 + s) % P] == '0');
                if (s < S) step(&r, W[(ph0 + s + 1) % P] - '0');
                if (r.nw >= MAXW - 2) { fprintf(stderr, "overflow\n"); return 1; }
            }
            // find period Q of col1 on white phases over [S/2, S]
            long Q = -1;
            for (long q = P; q <= 1024; q += P) {
                int ok = 1;
                for (long s = S / 2; s + q <= S; s++) if (wh[s] && col1[s] != col1[s + q]) { ok = 0; break; }
                if (ok) { Q = q; break; }
            }
            if (Q < 0) { naper++; if (naper < 5) printf("aperiodic: d=%u ph0=%d\n", d, ph0); continue; }
            // lock time: last s with wh[s] and col1[s] != col1[s+Q] (s+Q <= S), plus 1
            long tau = 0;
            for (long s = S - Q; s >= 0; s--) if (wh[s] && col1[s] != col1[s + Q]) { tau = s + 1; break; }
            int bk = 0; long e = tau; while (e) { bk++; e >>= 1; } tauhist[bk]++;
            if (tau > maxtau) { maxtau = tau; argd = d; argph = ph0; }
        }
    }
    printf("w=%s n=%d S=%ld d in [%u,%u): aperiodic=%ld max lock time=%ld (d=%u ph0=%d) log2hist:", W, n, S, dlo, dhi, naper, maxtau, argd, argph);
    for (int i = 0; i < 32; i++) if (tauhist[i]) printf(" [%d]%ld", i, tauhist[i]);
    printf("\n");
    return 0;
}
