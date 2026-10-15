// Verifier: same greatest-fixed-point wall search as gfpwall.c, with a bitset (1 bit per state) for large b.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static const char *e3[12] = {"001","001","011","110","010","010","110","101","100","100","101","011"};
static const char *e4[7] = {"0011","0110","1101","0101","0011","0001","0001"};
int main(int argc, char **argv) {
    int N, P, E[16][4];
    if (!strcmp(argv[1], "p3")) { N = 12; P = 3; for (int j = 0; j < N; j++) for (int f = 0; f < P; f++) E[j][f] = e3[j][f] - '0'; }
    else { N = 7; P = 4; for (int j = 0; j < N; j++) for (int f = 0; f < P; f++) E[j][f] = e4[j][f] - '0'; }
    int a = atoi(argv[2]) % N, b = atoi(argv[3]);
    uint64_t M = 1ULL << b, mask = M - 1, MW = M / 64;
    uint64_t *S = calloc((size_t)P * MW, 8);
    long long cnt = 0;
    for (int f = 0; f < P; f++) for (uint64_t r = 0; r < M; r++) {
        int u = E[a][f] ? 1 : (int)(r & 1) == E[(a + 1) % N][f];
        if (u) { S[f * MW + (r >> 6)] |= 1ULL << (r & 63); cnt++; }
    }
    int sweeps = 0, changed = 1;
    while (changed) {
        changed = 0; sweeps++;
        for (int f = 0; f < P; f++) {
            uint64_t ain = (uint64_t)E[a][f]; int g = (f + 1) % P; uint64_t *Sg = S + (size_t)g * MW, *Sf = S + (size_t)f * MW;
            for (uint64_t wi = 0; wi < MW; wi++) {
                uint64_t word = Sf[wi];
                while (word) {
                    int bit = __builtin_ctzll(word); word &= word - 1;
                    uint64_t r = (wi << 6) | (uint64_t)bit;
                    uint64_t s0 = (((r << 1) | ain) ^ (r | (r >> 1))) & mask;
                    uint64_t s1 = (((r << 1) | ain) ^ (r | (r >> 1) | (1ULL << (b - 1)))) & mask;
                    if (!((Sg[s0 >> 6] >> (s0 & 63)) & 1) || !((Sg[s1 >> 6] >> (s1 & 63)) & 1)) { Sf[wi] &= ~(1ULL << bit); cnt--; changed = 1; }
                }
            }
        }
    }
    printf("%s a=%d b=%d: maximal closed U-set size %lld (sweeps %d)\n", argv[1], a, b, cnt, sweeps);
    free(S); return 0;
}
