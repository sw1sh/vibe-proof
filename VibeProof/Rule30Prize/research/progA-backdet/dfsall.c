// like dfs.c but print all configs (x0 strings) achieving death time >= THR
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NW 4
typedef struct { uint64_t w[NW]; } bs;
static int W, MAXD, THR;
static unsigned char x0[300];
static inline void prefix_excl(const bs *g, bs *out, int nbits) {
    uint64_t carry = 0;
    for (int i = 0; i < NW; i++) {
        uint64_t v = g->w[i];
        v ^= v << 1; v ^= v << 2; v ^= v << 4; v ^= v << 8; v ^= v << 16; v ^= v << 32;
        uint64_t incl = v ^ (carry ? ~0ULL : 0ULL);
        out->w[i] = (incl << 1) | (carry ? 1ULL : 0ULL);
        carry = (incl >> 63) & 1ULL;
    }
    for (int i = 0; i < NW; i++) { int lo = i * 64;
        if (nbits <= lo) out->w[i] = 0; else if (nbits < lo + 64) out->w[i] &= ((1ULL << (nbits - lo)) - 1); }
}
static inline int getbit(const bs *b, int t) { return (b->w[t >> 6] >> (t & 63)) & 1; }
static void emit(int death) {
    printf("%d ", death);
    for (int k = 1; k <= W; k++) putchar('0' + x0[k]);
    putchar('\n');
}
static void rec(const bs *Am1, const bs *A, int n) {
    if (n >= MAXD) { emit(n); return; }
    bs g, P, An1;
    for (int i = 0; i < NW; i++) g.w[i] = A->w[i] | Am1->w[i];
    prefix_excl(&g, &P, n + 1);
    int an_if0 = getbit(&P, n);
    for (int v = 0; v <= 1; v++) {
        if (n + 1 > W && v == 1) continue;
        int an = an_if0 ^ v;
        if ((n % 2 == 0) && an != 1) { if (n >= THR && n + 1 > W) emit(n); continue; }
        x0[n + 1] = v;
        for (int i = 0; i < NW; i++) An1.w[i] = P.w[i] ^ (v ? ~0ULL : 0ULL);
        for (int i = 0; i < NW; i++) { int lo = i * 64, nb = n + 1;
            if (nb <= lo) An1.w[i] = 0; else if (nb < lo + 64) An1.w[i] &= ((1ULL << (nb - lo)) - 1); }
        rec(A, &An1, n + 1);
        x0[n + 1] = 0;
    }
}
int main(int argc, char **argv) {
    W = atoi(argv[1]); THR = atoi(argv[2]); MAXD = 250;
    bs Z; memset(&Z, 0, sizeof Z);
    rec(&Z, &Z, 0);
    return 0;
}
