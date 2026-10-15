// Left-only problem (LOP) faking horizon.
// Left half p <= -1 driven by column 0 = c(t) = w[t mod P] (t >= 0), started from a finite configuration
// supported on [-M, -1].  Condition (L): whenever c(t) = 1, col_{-1}(t) must equal !c(t+1).
// col_{-1}(k) depends permutively on config(-1-k), so for k < M the bit config(-1-k) is forced when
// c(k) = 1 and free when c(k) = 0.  For k >= M all config bits are 0 and (L) is a genuine check.
// We enumerate all free choices and report the maximal horizon H (first k with (L) violated).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NW 8   // 512 bits of left half
typedef struct { uint64_t w[NW]; } BS;
static inline int getb(const BS *s, int i) { return (s->w[i >> 6] >> (i & 63)) & 1; }
static inline void setb(BS *s, int i, int v) { if (v) s->w[i >> 6] |= 1ULL << (i & 63); else s->w[i >> 6] &= ~(1ULL << (i & 63)); }
// bit i <-> p = -(i+1). new(p) = old(p-1) ^ (old(p) | old(p+1)); old(p-1) is bit i+1, old(p+1) is bit i-1 (bit -1 = c)
static void step(BS *s, int c) {
    BS left, right, n;
    for (int k = 0; k < NW; k++) {
        left.w[k] = (s->w[k] >> 1) | (k + 1 < NW ? s->w[k + 1] << 63 : 0);
        right.w[k] = (s->w[k] << 1) | (k > 0 ? s->w[k - 1] >> 63 : (uint64_t)c);
    }
    for (int k = 0; k < NW; k++) n.w[k] = left.w[k] ^ (s->w[k] | right.w[k]);
    *s = n;
}
static const char *W; static int P, M, HMAX;
static int best; static long long nbest, count_ge;
static int cval(int t) { return W[t % P] - '0'; }
// Simulate from a full configuration and return the horizon.
static int horizon(const BS *cfg) {
    BS s = *cfg;
    for (int t = 0; t < HMAX; t++) {
        int ct = cval(t);
        if (ct == 1 && getb(&s, 0) != !cval(t + 1)) return t;
        step(&s, ct);
    }
    return HMAX;
}
// DFS: decide config bits one at a time. To get forced bits we need col_{-1}(k) with config(-1-k)=0 vs 1.
// Simple approach: build config incrementally; at step k evaluate col_{-1}(k) from the config prefix
// (bits beyond k do not influence col_{-1}(k)).
static int colm1_at(const BS *cfg, int k) {
    BS s = *cfg;
    for (int t = 0; t < k; t++) step(&s, cval(t));
    return getb(&s, 0);
}
static void dfs(BS *cfg, int k) {
    if (k == M) {
        int h = horizon(cfg);
        if (h > best) { best = h; nbest = 1; } else if (h == best) nbest++;
        if (h >= 2 * M) count_ge++;
        return;
    }
    int ck = cval(k);
    if (ck == 1) {
        setb(cfg, k, 0);
        int v0 = colm1_at(cfg, k);
        int need = !cval(k + 1);
        setb(cfg, k, v0 == need ? 0 : 1);
        dfs(cfg, k + 1);
        setb(cfg, k, 0);
    } else {
        setb(cfg, k, 0); dfs(cfg, k + 1);
        setb(cfg, k, 1); dfs(cfg, k + 1);
        setb(cfg, k, 0);
    }
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W);
    int M0 = atoi(argv[2]), M1 = atoi(argv[3]);
    HMAX = argc > 4 ? atoi(argv[4]) : 400;
    for (M = M0; M <= M1; M++) {
        BS cfg; memset(&cfg, 0, sizeof cfg);
        best = -1; nbest = 0; count_ge = 0;
        dfs(&cfg, 0);
        printf("w=%s M=%d maxH=%d (#=%lld) H/M=%.3f  #configs with H>=2M: %lld\n", W, M, best, nbest, (double)best / M, count_ge);
        fflush(stdout);
    }
    return 0;
}
