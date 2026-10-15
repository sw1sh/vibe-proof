// Exact light-cone forcing blocks for rule 30's right half driven at column 0.
// For each block u (length <= L), R(u) = set of states of cols 1..K (K = L+1) reachable after applying u from ALL states
// (column K+1 free). col1 after u is forced iff constant on R(u) (exact since col1 at time |u| <= L depends on cols 1..|u|+1).
// Print minimal forcing blocks (u forced, its proper suffix u[1:] not forced), with forced value.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int K, L; static uint32_t N, MASK;
static uint8_t *mark;
static char buf[64];
static int forced_val[1 << 22]; // index by (len, bits) -> -1 not forced, 0/1 forced ; we store via map below
// we store forcing info in a table keyed by (len, code) where code = bits of u (first char = most significant)
static int8_t *tab[24];
static inline uint32_t succ(uint32_t s, int c, int a) {
    return ((((s << 1) | (uint32_t)c) ^ (s | (s >> 1) | ((uint32_t)a << (K - 1))))) & MASK;
}
static void dfs(uint32_t *set, size_t n, int len, uint32_t code) {
    // record forcing of col1
    int h0 = 0, h1 = 0;
    for (size_t i = 0; i < n && !(h0 && h1); i++) { if (set[i] & 1) h1 = 1; else h0 = 1; }
    tab[len][code] = (h0 && h1) ? -1 : (h0 ? 0 : 1);
    if (len == L) return;
    for (int c = 0; c < 2; c++) {
        size_t m = 0;
        uint32_t *nset = malloc(sizeof(uint32_t) * (n * 2 < N ? n * 2 : N));
        for (size_t i = 0; i < n; i++) for (int a = 0; a < 2; a++) {
            uint32_t t = succ(set[i], c, a);
            if (!mark[t]) { mark[t] = 1; nset[m++] = t; }
        }
        for (size_t i = 0; i < m; i++) mark[nset[i]] = 0;
        dfs(nset, m, len + 1, (code << 1) | (uint32_t)c);
        free(nset);
    }
}
int main(int argc, char **argv) {
    L = atoi(argv[1]); K = L + 1; N = 1u << K; MASK = N - 1;
    mark = calloc(N, 1);
    for (int l = 0; l <= L; l++) tab[l] = malloc((size_t)1 << l);
    uint32_t *all = malloc(sizeof(uint32_t) * N);
    for (uint32_t s = 0; s < N; s++) all[s] = s;
    dfs(all, N, 0, 0);
    // minimal forcing blocks: u forced and u without its FIRST letter not forced
    long cnt[24] = {0}, tot[24] = {0};
    for (int l = 1; l <= L; l++) {
        for (uint32_t code = 0; code < (1u << l); code++) {
            if (tab[l][code] >= 0) tot[l]++;
            uint32_t suffix = code & ((1u << (l - 1)) - 1);
            if (tab[l][code] >= 0 && tab[l - 1][suffix] < 0) {
                cnt[l]++;
                for (int i = 0; i < l; i++) buf[i] = '0' + ((code >> (l - 1 - i)) & 1);
                buf[l] = 0;
                printf("min %s -> %d\n", buf, tab[l][code]);
            }
        }
    }
    for (int l = 1; l <= L; l++) printf("len %d: forcing blocks %ld of %ld (%.4f), minimal %ld\n", l, tot[l], 1L << l, (double)tot[l] / (1L << l), cnt[l]);
    return 0;
}
