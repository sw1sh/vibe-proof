// Spatially periodic infinite initial right halves x(p) = u[(p-1) mod q], p >= 1 (simulated on a width S+200 window,
// which is exact for the leftmost 64 columns over S steps), driver w^inf from phase ph0. Test entry into the
// ether+wall family (wall U-set at width bw). Enumerate all u of length q (q <= 16).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 1024
static const char *E[7] = {"0011", "0110", "1101", "0101", "0011", "0001", "0001"};
static int P, bw; static const char *W; static uint8_t *WALL;
static int nal; static int al_j[8], al_s[8];
static uint64_t erow[7][4];
typedef struct { uint64_t a[MAXW]; int nw; } Row;
static inline void step(Row *r, int c) {
    int nw = r->nw; uint64_t prev_hi = 0;
    for (int i = 0; i < nw; i++) {
        uint64_t x = r->a[i];
        uint64_t left = (x << 1) | prev_hi;
        uint64_t nxt = (i + 1 < nw) ? r->a[i + 1] : 0;
        uint64_t right = (x >> 1) | (nxt << 63);
        prev_hi = x >> 63;
        r->a[i] = left ^ (x | right);
    }
    r->a[0] = (r->a[0] & ~1ULL) | (uint64_t)c;
}
static int member(const Row *r, int psi) {
    uint64_t strip = (r->a[0] >> 1) | (r->nw > 1 ? (r->a[1] << 63) : 0);
    for (int a = 0; a < nal; a++) {
        int j0 = al_j[a], phi = (psi + al_s[a]) % 4;
        uint64_t diff = strip ^ erow[j0][phi];
        int agree = diff ? __builtin_ctzll(diff) : 64;
        int k = ((2 - j0) % 7 + 7) % 7;
        for (; k <= agree && k + bw <= 64; k += 7) {
            uint32_t ws = (uint32_t)((strip >> k) & ((1ULL << bw) - 1));
            if (WALL[((uint32_t)phi << bw) | ws]) return k;
        }
    }
    return -1;
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); bw = atoi(argv[2]);
    FILE *f = fopen(argv[3], "rb"); uint32_t N = 4u << bw; WALL = malloc(N);
    if (fread(WALL, 1, N, f) != N) return 1; fclose(f);
    int q = atoi(argv[4]); long S = atol(argv[5]);
    for (int j = 0; j < 7; j++) for (int s = 0; s < 4; s++) {
        int ok = 1; for (int ph = 0; ph < 4; ph++) if (E[j][ph] != W[((ph - s) % 4 + 4) % 4]) ok = 0;
        if (ok) { al_j[nal] = j; al_s[nal] = s; nal++; }
    }
    for (int j = 0; j < 7; j++) for (int ph = 0; ph < 4; ph++) { uint64_t m = 0; for (int p = 1; p <= 64; p++) if (E[(j + p) % 7][ph] == '1') m |= 1ULL << (p - 1); erow[j][ph] = m; }
    int nw = (int)((S + 256) / 64 + 1); if (nw > MAXW) return 1;
    static Row r; long fails = 0, total = 0, maxe = -1, naper = 0;
    for (uint32_t u = 0; u < (1u << q); u++) {
        for (int ph0 = 0; ph0 < P; ph0++) {
            memset(r.a, 0, sizeof r.a); r.nw = nw;
            for (int p = 1; p < nw * 64; p++) if ((u >> ((p - 1) % q)) & 1) r.a[p >> 6] |= 1ULL << (p & 63);
            r.a[0] = (r.a[0] & ~1ULL) | (uint64_t)(W[ph0] - '0');
            long e = -1; static uint8_t c1[200000], whv[200000];
            for (long s2 = 0; s2 <= S; s2++) {
                c1[s2] = (r.a[0] >> 1) & 1; whv[s2] = W[(ph0 + s2) % P] == '0';
                if (e < 0 && member(&r, (int)((ph0 + s2) % P)) >= 0) { e = s2; }
                step(&r, W[(ph0 + s2 + 1) % P] - '0');
            }
            total++;
            if (e < 0) {
                fails++;
                int okp = 0;
                for (long qq = P; qq <= 1024 && !okp; qq += P) { int ok = 1; for (long s2 = S / 2; s2 + qq <= S; s2++) if (whv[s2] && c1[s2] != c1[s2 + qq]) { ok = 0; break; } if (ok) okp = 1; }
                if (!okp) { naper++; if (naper <= 8) printf("APERIODIC col1-white: u=%u (q=%d) ph0=%d\n", u, q, ph0); }
            }
            else if (e > maxe) maxe = e;
        }
    }
    printf("w=%s q=%d S=%ld runs=%ld no-family-entry=%ld of which col1-white aperiodic=%ld; max entry=%ld\n", W, q, S, total, fails, naper, maxe);
    return 0;
}
