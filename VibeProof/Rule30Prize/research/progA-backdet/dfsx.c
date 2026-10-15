// DFS over finite ZBL configs (support <= W) with constraint a_t=1 at even t, and f_s=a_{2s+1} restricted:
// mode 0: no restriction; mode 1: f has no "00" and runs of 1s <= 4 ; mode 2: runs of 1s in {1,2,4} (zeros isolated)
// (run restriction applied to complete runs; the initial run (before the first 0) may be any length <= 4 in mode 1/2)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NW 4
typedef struct { uint64_t w[NW]; } bs;
static int W, MAXD, MODE;
static int best; static long long nleaves;
static unsigned char x0[300], bestx[300];
static long long hist[600];
static inline void prefix_excl(const bs *g, bs *out, int nbits) {
    uint64_t carry = 0;
    for (int i = 0; i < NW; i++) {
        uint64_t v = g->w[i];
        v ^= v << 1; v ^= v << 2; v ^= v << 4; v ^= v << 8; v ^= v << 16; v ^= v << 32;
        uint64_t incl = v ^ (carry ? ~0ULL : 0ULL);
        uint64_t excl = (incl << 1) | (carry ? 1ULL : 0ULL);
        out->w[i] = excl;
        carry = (incl >> 63) & 1ULL;
    }
    for (int i = 0; i < NW; i++) {
        int lo = i * 64;
        if (nbits <= lo) out->w[i] = 0;
        else if (nbits < lo + 64) out->w[i] &= ((1ULL << (nbits - lo)) - 1);
    }
}
static inline int getbit(const bs *b, int t) { return (b->w[t >> 6] >> (t & 63)) & 1; }
// f-state: lastf (-1 none, 0, 1), run (current run length of 1s), seen0 (whether a 0 has occurred)
static int allowed(int lastf, int run, int seen0, int nf) {
    if (MODE == 0) return 1;
    if (MODE == 3) return !(lastf == 0 && nf == 0);
    if (nf == 0) { if (lastf == 0) return 0; return 1; }
    // nf == 1
    if (run + 1 > 4) return 0;
    return 1;
}
static int run_ok_on_close(int run, int seen0) {
    // closing a run of 1s by a 0: in mode 2, complete runs (after a previous 0) must be 1,2,4
    if (MODE == 2 && seen0) return (run == 1 || run == 2 || run == 4);
    return 1;
}
static void rec(const bs *Am1, const bs *A, int n, int lastf, int run, int seen0) {
    if (n >= MAXD) { if (n > best) { best = n; memcpy(bestx, x0, sizeof x0); } hist[n]++; return; }
    bs g, P, An1;
    for (int i = 0; i < NW; i++) g.w[i] = A->w[i] | Am1->w[i];
    prefix_excl(&g, &P, n + 1);
    int an_if0 = getbit(&P, n);
    for (int v = 0; v <= 1; v++) {
        if (n + 1 > W && v == 1) continue;
        int an = an_if0 ^ v;
        int nl = lastf, nr = run, ns = seen0;
        if (n % 2 == 0) {
            if (an != 1) { if (n > best) { best = n; memcpy(bestx, x0, sizeof x0); bestx[n+1] = v; } hist[n]++; continue; }
        } else {
            // an is f_{(n-1)/2}
            if (!allowed(lastf, run, seen0, an)) { if (n > best) { best = n; memcpy(bestx, x0, sizeof x0); bestx[n+1]=v; } hist[n]++; continue; }
            if (an == 0) { if (!run_ok_on_close(run, seen0)) { if (n > best) { best = n; memcpy(bestx, x0, sizeof x0); bestx[n+1]=v;} hist[n]++; continue; } nl = 0; nr = 0; ns = 1; }
            else { nl = 1; nr = run + 1; }
        }
        x0[n + 1] = v;
        for (int i = 0; i < NW; i++) An1.w[i] = P.w[i] ^ (v ? ~0ULL : 0ULL);
        for (int i = 0; i < NW; i++) {
            int lo = i * 64, nb = n + 1;
            if (nb <= lo) An1.w[i] = 0;
            else if (nb < lo + 64) An1.w[i] &= ((1ULL << (nb - lo)) - 1);
        }
        rec(A, &An1, n + 1, nl, nr, ns);
        x0[n + 1] = 0;
    }
}
int main(int argc, char **argv) {
    W = atoi(argv[1]); MODE = atoi(argv[2]); MAXD = argc > 3 ? atoi(argv[3]) : 250;
    bs Z; memset(&Z, 0, sizeof Z);
    best = -1;
    rec(&Z, &Z, 0, -1, 0, 0);
    printf("W=%d mode=%d best death time=%d  (death-W=%d)  x0=", W, MODE, best, best - W);
    for (int k = 1; k <= W; k++) printf("%d", bestx[k]);
    printf("\n");
    return 0;
}
