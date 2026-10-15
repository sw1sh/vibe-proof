// Bottom-SCC probe for wider strips: random walk (random right inputs) from the zero state, then the
// closure (all inputs) of the reached state; repeat from a far point of the closure and compare sizes.
// Reports the closure size and which (phase, first-cell) pairs occur (U needs: at white phases of E[a],
// first cell == E[a+1][phase]).  usage: wall3b a b walklen
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static const char *E[12] = {"001","001","011","110","010","010","110","101","100","100","101","011"};
static int b, A; static uint64_t M;
static inline uint64_t stp(int a, int z, uint64_t r) {
    unsigned __int128 full = (unsigned __int128)a | ((unsigned __int128)r << 1) | ((unsigned __int128)z << (b + 1));
    return (uint64_t)((full ^ ((full >> 1) | (full >> 2))) & (unsigned __int128)(M - 1));
}
static inline uint64_t succ(uint64_t v, int z) { int phi = (int)(v / M); uint64_t r = v % M; return (uint64_t)((phi + 1) % 3) * M + stp(E[A][phi] - '0', z, r); }
static uint64_t *bm; static uint64_t *q;
static uint64_t closure(uint64_t v0, int pairs[3][2], uint64_t *far) {
    uint64_t N = 3 * M; memset(bm, 0, (N + 63) / 64 * 8);
    uint64_t qh = 0, qt = 0; q[qt++] = v0; bm[v0 >> 6] |= 1ULL << (v0 & 63);
    memset(pairs, 0, sizeof(int) * 6);
    while (qh < qt) { uint64_t v = q[qh++]; pairs[v / M][(v % M) & 1] = 1;
        for (int z = 0; z < 2; z++) { uint64_t u = succ(v, z); if (!(bm[u >> 6] >> (u & 63) & 1)) { bm[u >> 6] |= 1ULL << (u & 63); q[qt++] = u; if (qt > 40000000ULL) { fprintf(stderr, "too big\n"); exit(1); } } } }
    *far = q[qt - 1]; return qt;
}
int main(int argc, char **argv) {
    A = atoi(argv[1]); b = atoi(argv[2]); long walk = atol(argv[3]); M = 1ULL << b; uint64_t N = 3 * M;
    bm = malloc((N + 63) / 64 * 8); q = malloc(sizeof(uint64_t) * 40000001ULL);
    uint64_t rs = 0x9E3779B97F4A7C15ULL, v = 0;
    for (long i = 0; i < walk; i++) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; v = succ(v, (int)(rs & 1)); }
    int pairs[3][2]; uint64_t far, far2; uint64_t c1 = closure(v, pairs, &far);
    int pairs2[3][2]; uint64_t c2 = closure(far, pairs2, &far2);
    printf("a=%d (%s|%s) b=%d: closure(walk end)=%llu closure(far)=%llu; (phase,first cell) pairs present:", A, E[A], E[(A+1)%12], b,
           (unsigned long long)c1, (unsigned long long)c2);
    int uviol = 0;
    for (int phi = 0; phi < 3; phi++) for (int x = 0; x < 2; x++) if (pairs2[phi][x]) {
        printf(" (%d,%d)", phi, x); if (E[A][phi] == '0' && x != E[(A+1)%12][phi] - '0') uviol = 1; }
    printf("  U %s\n", uviol ? "VIOLATED" : "holds");
    return 0;
}
