// Closure (all right inputs) of a seed strip state of width b <= 120, driven by column 0 = w (period P).
// Seed: right half driven by c = 1, then w^inf, at time T0 (columns 1..b).  Reports the closure size (capped),
// and whether column 1 at white phases is consistently labelled (good) on the closure.
// usage: closure w b T0 cap
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int P, b; static const char *W; static u128 MASK;
static inline u128 stp(int a, int z, u128 r) {
    // full: bit0 = a, bits 1..b = r, bit b+1 = z ; compute on (b+2) <= 122 bits
    u128 full = (u128)a | (r << 1) | ((u128)z << (b + 1));
    return (full ^ ((full >> 1) | (full >> 2))) & MASK;
}
typedef struct { u128 r; int8_t ph; int8_t used; int16_t lab; } ent;
static ent *H; static size_t cap, cnt;
static size_t hidx(int ph, u128 r) { uint64_t lo = (uint64_t)r, hi = (uint64_t)(r >> 64); uint64_t h = (lo * 0x9E3779B97F4A7C15ULL) ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ ((uint64_t)ph * 0x165667B19E3779F9ULL); h ^= h >> 29; return (size_t)(h & (cap - 1)); }
static int labbad = 0;
static int insert(int ph, u128 r, int lab) { size_t i = hidx(ph, r); while (H[i].used) { if (H[i].ph == ph && H[i].r == r) { if (H[i].lab != lab) labbad = 1; return 0; } i = (i + 1) & (cap - 1); } H[i].used = 1; H[i].ph = (int8_t)ph; H[i].r = r; H[i].lab = (int16_t)lab; cnt++; return 1; }
static int getlab(int ph, u128 r) { size_t i = hidx(ph, r); while (H[i].used) { if (H[i].ph == ph && H[i].r == r) return H[i].lab; i = (i + 1) & (cap - 1); } return -1; }
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); b = atoi(argv[2]); long T0 = atol(argv[3]); size_t CAP = (size_t)atol(argv[4]); int LBL = argc > 5 ? atoi(argv[5]) : 21;
    MASK = (b == 128) ? ~(u128)0 : (((u128)1 << b) - 1);
    // simulate the driven right half (columns 1..L) for T0 steps, exact on columns 1..b (light cone)
    int L = b + (int)T0 + 4; uint8_t *row = calloc(L + 2, 1), *nw = calloc(L + 2, 1); // row[p], p = 0..L
    for (long t = 0; t < T0; t++) {
        int c = (t == 0) ? 1 : W[(t - 1) % P] - '0'; row[0] = (uint8_t)c;
        for (int p = 1; p <= L; p++) nw[p] = row[p - 1] ^ (row[p] | (p + 1 <= L ? row[p + 1] : 0));
        memcpy(row + 1, nw + 1, L);
    }
    int ph0 = (int)((T0 - 1) % P); // phase of c(T0) = W[(T0-1) % P]
    u128 r0 = 0; for (int i = 0; i < b; i++) if (row[i + 1]) r0 |= (u128)1 << i;
    cap = 1; while (cap < 2 * CAP + 16) cap <<= 1; H = calloc(cap, sizeof(ent)); cnt = 0;
    u128 *qr = malloc(sizeof(u128) * (CAP + 4)); int8_t *qp = malloc(CAP + 4); size_t qh = 0, qt = 0;
    insert(ph0, r0, 0); qr[qt] = r0; qp[qt] = (int8_t)ph0; qt++;
    int overflow = 0;
    while (qh < qt) {
        u128 r = qr[qh]; int ph = qp[qh]; qh++; int lab = getlab(ph, r);
        int a = W[ph] - '0';
        for (int z = 0; z < 2; z++) { u128 r2 = stp(a, z, r); int ph2 = (ph + 1) % P;
            if (insert(ph2, r2, (lab + 1) % LBL)) { if (qt >= CAP) { overflow = 1; break; } qr[qt] = r2; qp[qt] = (int8_t)ph2; qt++; } }
        if (overflow) break;
    }
    if (overflow) { printf("w=%s b=%d T0=%ld: closure exceeds cap %zu\n", W, b, T0, CAP); return 0; }
    // consistency of column 1 at white phases: does each (phase) see a single col1 value? (period-P labelling check)
    int seen[16][2] = {{0}};
    for (size_t i = 0; i < qt; i++) if (W[qp[i]] == '0') seen[qp[i]][(int)(qr[i] & 1)] = 1;
    printf("w=%s b=%d T0=%ld: closure size %zu; col1 values at white phases:", W, b, T0, qt);
    for (int ph = 0; ph < P; ph++) if (W[ph] == '0') printf(" ph%d:{%s%s}", ph, seen[ph][0] ? "0" : "", seen[ph][1] ? "1" : "");
    // find the first column that varies over the closure
    int firstvar = -1;
    for (int p = 0; p < b && firstvar < 0; p++) { int v0[16] = {0}, v1[16] = {0};
        for (size_t i = 0; i < qt; i++) { if ((qr[i] >> p) & 1) v1[qp[i]] = 1; else v0[qp[i]] = 1; }
        for (int ph = 0; ph < P; ph++) if (v0[ph] && v1[ph]) { firstvar = p + 1; break; } }
    printf("; first column varying within a phase: %d", firstvar);
    // label consistency and col1-at-white as a function of the label
    int outv[4096]; for (int i = 0; i < LBL; i++) outv[i] = -1; int outbad = 0;
    for (size_t i = 0; i < qt; i++) { int lab = getlab(qp[i], qr[i]); if (W[qp[i]] == '0') { int v = (int)(qr[i] & 1); if (outv[lab] < 0) outv[lab] = v; else if (outv[lab] != v) outbad = 1; } }
    printf("; time-label mod %d %s; col1 at white times %s", LBL, labbad ? "INCONSISTENT" : "consistent", outbad ? "NOT a function of the label" : "a function of the label (periodic)");
    // first column that is not a function of the label
    int firstfree = -1;
    for (int p = 0; p < b && firstfree < 0; p++) { int val[4096]; for (int i = 0; i < LBL; i++) val[i] = -1;
        for (size_t i = 0; i < qt; i++) { int lab = getlab(qp[i], qr[i]); int v = (int)((qr[i] >> p) & 1); if (val[lab] < 0) val[lab] = v; else if (val[lab] != v) { firstfree = p + 1; break; } } }
    printf("; columns 1..%d are functions of the label\n", firstfree < 0 ? b : firstfree - 1);
    return 0;
}
