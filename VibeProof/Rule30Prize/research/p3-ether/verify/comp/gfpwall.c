// Verifier: greatest fixed point wall search. For an ether (ring N, period P), attachment column a, width b:
// S = maximal set of states (phase f, strip r in [0,2^b)) such that every state satisfies the U-property
// (if ether[a][f] == 0 then bit0(r) == ether[a+1][f]) and both successors (z = 0, 1) lie in S.
// S nonempty <=> a wall (in the sense of WallOK) exists. Output |S| per (a, b).
// usage: gfpwall p3|p4 a b
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N, P; static int E[16][4];
static const char *e3[12] = {"001","001","011","110","010","010","110","101","100","100","101","011"};
static const char *e4[7] = {"0011","0110","1101","0101","0011","0001","0001"};
int main(int argc, char **argv) {
    if (!strcmp(argv[1], "p3")) { N = 12; P = 3; for (int j = 0; j < N; j++) for (int f = 0; f < P; f++) E[j][f] = e3[j][f] - '0'; }
    else { N = 7; P = 4; for (int j = 0; j < N; j++) for (int f = 0; f < P; f++) E[j][f] = e4[j][f] - '0'; }
    int a = atoi(argv[2]) % N, b = atoi(argv[3]);
    uint64_t M = 1ULL << b, mask = M - 1;
    uint8_t *S = malloc((size_t)P * M);
    long long cnt = 0;
    for (int f = 0; f < P; f++) for (uint64_t r = 0; r < M; r++) {
        int u = E[a][f] ? 1 : (int)(r & 1) == E[(a + 1) % N][f];
        S[f * M + r] = (uint8_t)u; cnt += u;
    }
    int sweeps = 0; int changed = 1;
    while (changed) {
        changed = 0; sweeps++;
        for (int f = 0; f < P; f++) {
            uint64_t ain = (uint64_t)E[a][f]; int g = (f + 1) % P; uint8_t *Sg = S + (size_t)g * M, *Sf = S + (size_t)f * M;
            for (uint64_t r = 0; r < M; r++) {
                if (!Sf[r]) continue;
                uint64_t base = ((r << 1) | ain) ^ (r | (r >> 1));
                uint64_t s0 = base & mask, s1 = (base ^ (1ULL << (b - 1))) & mask;
                // with z=1 the right term gets bit b-1 set: (r | r>>1 | 1<<(b-1)); recompute exactly
                s1 = (((r << 1) | ain) ^ (r | (r >> 1) | (1ULL << (b - 1)))) & mask;
                if (!Sg[s0] || !Sg[s1]) { Sf[r] = 0; cnt--; changed = 1; }
            }
        }
    }
    printf("%s a=%d b=%d: maximal closed U-set size %lld (sweeps %d)\n", argv[1], a, b, cnt, sweeps);
    free(S); return 0;
}
