// Drive right half of rule 30 (p>=1) with periodic word w at phase ph, from initial config.
// Initial config: mode 0 = random of width W (seed), mode 1 = real rule30 right half at time W,
// mode 2 = zero config. Compute column 1 for N steps (truncate cells that cannot affect col 1).
// Report eventual period (T,P) of column 1 found in last half via KMP smallest period.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static u64 rng_s;
static u64 rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

// row bit i <-> column i+1
// one step: new[i] = old[i-1] ^ (old[i] | old[i+1]), old[-1] = c
static void step(u64 *row, int nw, int c) {
    u64 carry = (u64)c; // bit coming into position 0 from the left (column 0)
    for (int j = 0; j < nw; j++) {
        u64 cur = row[j];
        u64 nxt = (j + 1 < nw) ? row[j + 1] : 0;
        u64 left = (cur << 1) | carry;
        u64 right = (cur >> 1) | (nxt << 63);
        carry = cur >> 63;
        row[j] = left ^ (cur | right);
    }
}
int smallest_period(const uint8_t *s, int n) { // KMP
    int *f = malloc(sizeof(int) * (n + 1)); f[0] = -1; int k = -1;
    for (int i = 0; i < n; i++) { while (k >= 0 && s[k] != s[i]) k = f[k]; k++; f[i + 1] = k; }
    int p = n - f[n]; free(f); return p;
}
int main(int argc, char **argv) {
    const char *w = argv[1]; int ph = atoi(argv[2]); int mode = atoi(argv[3]); long W = atol(argv[4]);
    u64 seed = strtoull(argv[5], 0, 10); long N = atol(argv[6]);
    int P = strlen(w);
    rng_s = seed * 2654435761ULL + 88172645463325252ULL; for (int i = 0; i < 10; i++) rnd();
    long width = W + N + 64; int nw = (int)(width / 64 + 2);
    u64 *row = calloc(nw, sizeof(u64));
    if (mode == 0) { for (long i = 0; i < W; i++) if (rnd() & 1) row[i / 64] |= 1ULL << (i % 64); }
    else if (mode == 1) {
        // real rule 30 at time W: full row positions -W..W; compute with bitset of width 2W+3
        long L = 2 * W + 3; int nw2 = (int)(L / 64 + 2); u64 *r = calloc(nw2, sizeof(u64)), *t2 = calloc(nw2, sizeof(u64));
        long off = W + 1; // position p stored at bit p+off
        r[off / 64] |= 1ULL << (off % 64);
        for (long t = 0; t < W; t++) {
            // new[p] = old[p-1] ^ (old[p] | old[p+1]); bit b: old[b-1] is (r<<1), old[b+1] is (r>>1)
            for (int j = 0; j < nw2; j++) {
                u64 cur = r[j], prv = j ? r[j - 1] : 0, nx = (j + 1 < nw2) ? r[j + 1] : 0;
                u64 left = (cur << 1) | (prv >> 63), right = (cur >> 1) | (nx << 63);
                t2[j] = left ^ (cur | right);
            }
            memcpy(r, t2, nw2 * sizeof(u64));
        }
        for (long p = 1; p <= W; p++) { long b = p + off; if ((r[b / 64] >> (b % 64)) & 1) row[(p - 1) / 64] |= 1ULL << ((p - 1) % 64); }
        free(r); free(t2);
    }
    uint8_t *col = malloc(N);
    int wb[64]; for (int i = 0; i < P; i++) wb[i] = w[i] - '0';
    for (long t = 0; t < N; t++) {
        col[t] = row[0] & 1;
        // cells beyond column N - t + 1 cannot affect column 1 before time N: truncate words
        long need = (N - t) + 2; int nwa = (int)(need / 64 + 2); if (nwa > nw) nwa = nw;
        step(row, nwa, wb[(ph + t) % P]);
    }
    // eventual period: smallest period of last half
    long h = N / 2; int p = smallest_period(col + h, (int)(N - h));
    if (p > (N - h) / 3) { printf("%s ph=%d mode=%d W=%ld seed=%llu: APERIODIC? (last-half period %d)\n", w, ph, mode, W, (unsigned long long)seed, p); return 0; }
    long T = h; while (T > 0 && col[T - 1] == col[T - 1 + p]) T--;
    printf("%s ph=%d mode=%d W=%ld seed=%llu: T=%ld P=%d\n", w, ph, mode, W, (unsigned long long)seed, T, p);
    return 0;
}
