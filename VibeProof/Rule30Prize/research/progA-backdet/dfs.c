// DFS over finite ZBL configurations x_0 with support <= W satisfying a_t = 1 at even t.
// Anti-diagonal A_n(t) = x_t(n-t), t=0..n-1. A_{n+1}(t) = x0(n+1) ^ XOR_{s<t}(A_n(s)|A_{n-1}(s)).
// a_n = A_{n+1}(n). Constraint: a_n = 1 for even n.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NW 4
typedef struct { uint64_t w[NW]; } bs;
static int W, MAXD;
static int best; static int bestcount;
static unsigned char x0[300], bestx[300];
static long long hist[600];
static inline void prefix_excl(const bs *g, bs *out, int nbits) {
    // out(t) = XOR_{s<t} g(s), for t = 0..nbits-1
    uint64_t carry = 0;
    for (int i = 0; i < NW; i++) {
        uint64_t v = g->w[i];
        // inclusive prefix within word
        v ^= v << 1; v ^= v << 2; v ^= v << 4; v ^= v << 8; v ^= v << 16; v ^= v << 32;
        // exclusive: shift by one, bring in carry
        uint64_t incl = v ^ (carry ? ~0ULL : 0ULL);
        uint64_t excl = (incl << 1) | (carry ? 1ULL : 0ULL);
        // careful: excl bit0 = carry (xor of all previous words), bit t = incl(t-1)
        out->w[i] = excl;
        carry = (incl >> 63) & 1ULL;
    }
    // mask to nbits
    for (int i = 0; i < NW; i++) {
        int lo = i * 64;
        if (nbits <= lo) out->w[i] = 0;
        else if (nbits < lo + 64) out->w[i] &= ((1ULL << (nbits - lo)) - 1);
    }
}
static inline int getbit(const bs *b, int t) { return (b->w[t >> 6] >> (t & 63)) & 1; }
static void rec(const bs *Am1, const bs *A, int n) {
    // A = A_n (bits 0..n-1), Am1 = A_{n-1}. Choose x0(n+1).
    if (n >= MAXD) { // survived to depth MAXD
        if (n > best) { best = n; memcpy(bestx, x0, sizeof x0); bestcount = 0; }
        if (n == best) bestcount++;
        hist[n]++;
        return;
    }
    bs g, P, An1;
    for (int i = 0; i < NW; i++) g.w[i] = A->w[i] | Am1->w[i];
    // mask g to bits 0..n-1 (Am1 has bits 0..n-2 so fine, A has 0..n-1)
    prefix_excl(&g, &P, n + 1);  // P(t) for t=0..n
    int an_if0 = getbit(&P, n);
    for (int v = 0; v <= 1; v++) {
        if (n + 1 > W && v == 1) continue;
        int an = an_if0 ^ v;
        if ((n % 2 == 0) && an != 1) {
            // death at time n
            if (n > best) { best = n; memcpy(bestx, x0, sizeof x0); bestx[n+1] = v; bestcount = 0; }
            if (n == best) bestcount++;
            hist[n]++;
            continue;
        }
        x0[n + 1] = v;
        for (int i = 0; i < NW; i++) An1.w[i] = P.w[i] ^ (v ? ~0ULL : 0ULL);
        // mask to bits 0..n
        for (int i = 0; i < NW; i++) {
            int lo = i * 64, nb = n + 1;
            if (nb <= lo) An1.w[i] = 0;
            else if (nb < lo + 64) An1.w[i] &= ((1ULL << (nb - lo)) - 1);
        }
        rec(A, &An1, n + 1);
        x0[n + 1] = 0;
    }
}
int main(int argc, char **argv) {
    W = atoi(argv[1]); MAXD = argc > 2 ? atoi(argv[2]) : 250;
    bs Z; memset(&Z, 0, sizeof Z);
    best = -1;
    // depth 0: A_0 is empty (no cells), A_{-1} empty.
    rec(&Z, &Z, 0);
    printf("W=%d best death time=%d count=%d\n", W, best, bestcount);
    printf("x0 (k=1..): ");
    for (int k = 1; k <= W; k++) printf("%d", bestx[k]);
    printf("\n");
    printf("death-time histogram: ");
    for (int i = 0; i < 600; i++) if (hist[i]) printf("%d:%lld ", i, hist[i]);
    printf("\n");
    return 0;
}
