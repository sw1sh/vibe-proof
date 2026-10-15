// Left-half consistency survival experiment for rule 30.
// Left half at time T: cells p=-1..-T, cell(T,-T)=1, zeros beyond.
// Driver c(t) = w[(t-T) mod P] for t >= T.  Forced constraint: c(t)=1 => x(t)=cell(t,-1) = 1-c(t+1).
// We enumerate (by DFS with the permutive triangle) exactly the states satisfying the forced
// constraints on [T, 2T-2] (and the forced value at 2T-1, cell(-T)=1), then forward-simulate each
// with bitsets to find its first violation time (or survival to horizon H).
// Usage: lsurv w Tmin Tmax Hfactor [verbose]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXT 64
#define MAXW 128   // words of 64 bits -> 8192 cells
static int P; static int wv[256];
static int T, H;
static int tri[MAXT + 2][MAXT + 2]; // tri[i][j] = cell(T+i, -j), j>=1, i+j <= depth+... ; tri[i][0] = c(T+i)
static long long nleaves, nsurv, maxfv; static long long hist[1 << 16];
static int verbose;
static int cdrv(int t) { return wv[((t - T) % P + P) % P]; }

static uint64_t row[MAXW], nrow[MAXW];

static long long simulate(void) {
    // build row at time T from tri[0][1..T]
    int nw = (H + 2) / 64 + 2; if (nw > MAXW) { fprintf(stderr, "H too large\n"); exit(1); }
    memset(row, 0, sizeof(uint64_t) * nw);
    for (int j = 1; j <= T; j++) if (tri[0][j]) row[(j - 1) >> 6] |= 1ULL << ((j - 1) & 63);
    for (int t = T; t < H; t++) {
        int x = row[0] & 1; int ct = cdrv(t);
        if (ct == 1 && x != 1 - cdrv(t + 1)) return t;
        int len = t + 1; // row length at time t+1 (bits 0..t)
        int lw = (len + 63) / 64;
        // right[i] = old[i-1], right[0] = c(t) ; left[i] = old[i+1]
        uint64_t carry = (uint64_t)ct;
        for (int k = 0; k < lw; k++) {
            uint64_t o = row[k];
            uint64_t r = (o << 1) | carry; carry = o >> 63;
            uint64_t l = (o >> 1) | ((k + 1 < MAXW ? row[k + 1] : 0) << 63);
            nrow[k] = l ^ (o | r);
        }
        // mask to len bits
        int rem = len & 63; if (rem) nrow[lw - 1] &= (1ULL << rem) - 1;
        for (int k = lw; k < nw; k++) nrow[k] = 0;
        memcpy(row, nrow, sizeof(uint64_t) * nw);
    }
    return -1; // survived
}

// DFS: depth d = number of cells chosen (cells -1..-d at time T). Choosing cell -(d+1) completes
// anti-diagonal i+j = d+1 and determines x(T+d) = tri[d][1].
static void dfs(int d) {
    if (d == T) {
        nleaves++;
        long long fv = simulate();
        if (fv < 0) { nsurv++; if (verbose) { printf("  survivor T=%d state(-1..-T)=", T); for (int j = 1; j <= T; j++) printf("%d", tri[0][j]); printf("\n"); } }
        else { if (fv > maxfv) maxfv = fv; if (fv - T < (1 << 16)) hist[fv - T]++; }
        return;
    }
    for (int v = 0; v <= 1; v++) {
        if (d == T - 1 && v == 0) continue; // cell -T must be 1
        tri[0][d + 1] = v;
        // fill anti-diagonal i + j = d+1 for i = 1..d
        for (int i = 1; i <= d; i++) {
            int j = d + 1 - i;
            int L = tri[i - 1][j + 1], C = tri[i - 1][j], R = tri[i - 1][j - 1];
            tri[i][j] = L ^ (C | R);
        }
        int t = T + d; int x = tri[d][1];
        if (cdrv(t) == 1 && x != 1 - cdrv(t + 1)) continue;
        dfs(d + 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: lsurv w Tmin Tmax Hfactor [verbose]\n"); return 1; }
    const char *w = argv[1]; P = strlen(w); for (int i = 0; i < P; i++) wv[i] = w[i] - '0';
    int Tmin = atoi(argv[2]), Tmax = atoi(argv[3]); double hf = atof(argv[4]); verbose = argc > 5 ? atoi(argv[5]) : 0;
    for (T = Tmin; T <= Tmax; T++) {
        H = (int)(hf * T) + 40;
        for (int i = 0; i <= T + 1; i++) tri[i][0] = cdrv(T + i);
        nleaves = nsurv = 0; maxfv = -1; memset(hist, 0, sizeof hist);
        dfs(0);
        // survival profile: number of leaves alive at time T + 2T, 3T ...
        long long alive2 = 0, alive3 = 0, alive4 = 0;
        for (long long k = 0; k < (1 << 16); k++) { if (k >= 2 * T) alive2 += hist[k]; if (k >= 3 * T) alive3 += hist[k]; if (k >= 4 * T) alive4 += hist[k]; }
        alive2 += nsurv; alive3 += nsurv; alive4 += nsurv;
        printf("w=%s T=%d leaves=%lld surv_to_H=%lld H=%d maxfirstviol=%lld (=T+%lld, ratio %.3f) alive@3T=%lld alive@4T=%lld alive@5T=%lld\n",
               w, T, nleaves, nsurv, H, maxfv, maxfv - T, maxfv >= 0 ? (double)maxfv / T : -1.0, alive2, alive3, alive4);
        fflush(stdout);
    }
    return 0;
}
