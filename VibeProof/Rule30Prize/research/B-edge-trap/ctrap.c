// Maximal closed "U-set" for the strip relaxation with left neighbour column L (periodic word, phase phi):
//   S0 = {(phi, s) : L[phi] = '0' -> s_1 = U[phi]},  S = greatest subset of S0 closed under all successors
//   (successor: s' = lin3(L[phi] :: s ++ [x]) for x in {0,1}; phase phi+1 mod P).
// Also: closure (reachable set under all inputs) from a given seed state, and membership tests.
// usage: ctrap L U b out.bin [seedphi seedstate]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int P, b; static const char *L, *U;
static inline uint32_t succ1(int phi, uint32_t s, int x) {
    // full: bit0 = column 0 = L[phi], bits 1..b = s, bit b+1 = x
    uint64_t full = (uint64_t)(L[phi] - '0') | ((uint64_t)s << 1) | ((uint64_t)x << (b + 1));
    uint64_t nw = full ^ ((full >> 1) | (full >> 2));
    return (uint32_t)(nw & ((1ULL << b) - 1));
}
int main(int argc, char **argv) {
    L = argv[1]; U = argv[2]; P = strlen(L); b = atoi(argv[3]);
    uint32_t N = (uint32_t)P << b, M = 1u << b;
    uint8_t *in = malloc(N);
    long cnt = 0;
    for (int phi = 0; phi < P; phi++) for (uint32_t s = 0; s < M; s++) {
        int ok = 1;
        if (L[phi] == '0' && U[phi] != '*') ok = ((int)(s & 1) == U[phi] - '0');
        in[((uint32_t)phi << b) | s] = (uint8_t)ok; cnt += ok;
    }
    int changed = 1, passes = 0;
    while (changed) {
        changed = 0; passes++;
        for (int phi = 0; phi < P; phi++) {
            int nphi = (phi + 1) % P;
            for (uint32_t s = 0; s < M; s++) {
                uint32_t id = ((uint32_t)phi << b) | s;
                if (!in[id]) continue;
                uint32_t a = succ1(phi, s, 0), c = succ1(phi, s, 1);
                if (!in[((uint32_t)nphi << b) | a] || !in[((uint32_t)nphi << b) | c]) { in[id] = 0; changed = 1; cnt--; }
            }
        }
    }
    long per[64] = {0};
    for (uint32_t id = 0; id < N; id++) per[id >> b] += in[id];
    printf("L=%s U=%s b=%d maximal closed U-set size %ld (passes %d) per phase:", L, U, b, cnt, passes);
    for (int phi = 0; phi < P; phi++) printf(" %ld", per[phi]);
    printf("\n");
    FILE *f = fopen(argv[4], "wb"); fwrite(in, 1, N, f); fclose(f);
    if (argc > 6) {
        int sphi = atoi(argv[5]); uint32_t sst = (uint32_t)strtoul(argv[6], 0, 10);
        uint8_t *seen = calloc(N, 1); uint32_t *q = malloc(sizeof(uint32_t) * N); uint32_t qh = 0, qt = 0;
        uint32_t id0 = ((uint32_t)sphi << b) | sst; seen[id0] = 1; q[qt++] = id0;
        while (qh < qt) {
            uint32_t id = q[qh++]; int phi = id >> b; uint32_t s = id & (M - 1);
            for (int x = 0; x < 2; x++) { uint32_t n2 = ((uint32_t)((phi + 1) % P) << b) | succ1(phi, s, x); if (!seen[n2]) { seen[n2] = 1; q[qt++] = n2; } }
        }
        long inside = 0; for (uint32_t i = 0; i < qt; i++) inside += in[q[i]];
        printf("closure of seed (%d,%u): %u states, %ld inside the maximal U-set\n", sphi, sst, qt, inside);
        if (argc > 7) { FILE *g = fopen(argv[7], "w"); for (uint32_t i = 0; i < qt; i++) fprintf(g, "%u %u\n", q[i] >> b, q[i] & (M - 1)); fclose(g); }
    }
    return 0;
}
