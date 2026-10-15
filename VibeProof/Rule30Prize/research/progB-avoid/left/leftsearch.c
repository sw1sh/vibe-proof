// Left-half constraint search (Program-A style) for period-4 words.
// Left half columns -1,-2,... evolve by rule 30 with an effective column 0 = cp (periodic, period 4).
// Constraint: column -1 follows pat (chars '0','1','y' (free bit of the block), 'n' (negated free bit)).
// Backward (left-permutive) reconstruction: given column -1 on times t0, t0+1, ..., the row at t0 is
// U[q][0], q = 1, 2, ...; U[0][t] = cp(t), U[1][t] = pat(t), U[q+1][t] = U[q][t+1] ^ (U[q][t] | U[q-1][t]).
// A finite row of support <= W at time t0 means U[q][0] = 0 for q > W.  DFS over the free bits; report the
// maximal depth D such that some choice of free bits makes U[q][0] = 0 for all W < q <= D.
// ("survival": the finite row keeps the constraint on column -1 up to time t0 + D - 1.)
// usage: leftsearch pat cp phase Wmin Wmax step cap
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXH 1200
static uint8_t U[MAXH + 2][MAXH + 2];
static const char *pat, *cp; static int phi, W, cap, best; static long nodes;
static uint8_t yv[MAXH];
static void addtime(int H) { // column -1 at time index H is set in U[1][H]; extend anti-diagonal
    for (int q = 2; q <= H + 1; q++) {
        int t = H + 1 - q;
        U[q][t] = U[q - 1][t + 1] ^ (U[q - 1][t] | U[q - 2][t]);
    }
}
static void dfs(int H) { // H = number of known times = current depth
    nodes++;
    if (H > best) best = H;
    if (H >= cap) return;
    int ph = (phi + H) % 4, blk = (phi + H) / 4;
    char ch = pat[ph];
    U[0][H] = cp[ph] - '0';
    int choices[2], nc = 0;
    if (ch == '0') { choices[0] = 0; nc = 1; }
    else if (ch == '1') { choices[0] = 1; nc = 1; }
    else {
        // free bit of block blk: if it already occurred in this block (pattern has two y's) reuse it
        int seen = 0; for (int h = H - 1; h >= 0 && (phi + h) / 4 == blk; h--) { char c2 = pat[(phi + h) % 4]; if (c2 == 'y' || c2 == 'n') { seen = 1; break; } }
        if (seen) { int v = yv[blk] ^ (ch == 'n'); choices[0] = v; nc = 1; }
        else { choices[0] = 0; choices[1] = 1; nc = 2; }
    }
    for (int i = 0; i < nc; i++) {
        int v = choices[i];
        if (ch == 'y' || ch == 'n') yv[blk] = (uint8_t)(v ^ (ch == 'n'));
        U[1][H] = (uint8_t)v;
        addtime(H);
        int depth = H + 1;
        if (depth > W && U[depth][0]) continue;  // row must vanish beyond W
        dfs(H + 1);
    }
}
int main(int argc, char **argv) {
    pat = argv[1]; cp = argv[2]; phi = atoi(argv[3]);
    int Wmin = atoi(argv[4]), Wmax = atoi(argv[5]), st = atoi(argv[6]); cap = atoi(argv[7]);
    if (cap > MAXH) cap = MAXH;
    for (W = Wmin; W <= Wmax; W += st) {
        best = 0; nodes = 0;
        dfs(0);
        printf("pat=%s cp=%s phase=%d W=%d: max survival depth %d (excess %d) nodes %ld\n", pat, cp, phi, W, best, best - W, nodes);
        fflush(stdout);
    }
    return 0;
}
