// Entry into the ether+wall trap family for the driven right half.
// Ether E (index j = 0..6: B1 B2 B3 B4 B5 c c), columns at ether phase 0..3. Driver w = ether column j0 with time shift s
// (column(phi) = w[(phi - s) mod 4]).  Family member (k): columns 1..k equal ether columns j0+1..j0+k (ether phase
// phi = psi + s), (j0 + k) mod 7 == 2 (B3), and columns k+1..k+bw form a state of the wall U-set at phase phi.
// Modes: entry2 w bw wallfile prefix n S        (all prefixes d of length n, all driver phases)
//        entry2 w bw wallfile true Ta:Tb:Ts S   (true center column prefixes)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 8192
static const char *E[7] = {"0011", "0110", "1101", "0101", "0011", "0001", "0001"};
static int P, bw; static const char *W; static uint8_t *WALL;
static int nal; static int al_j[8], al_s[8];
static uint64_t erow[7][4]; // erow[j0][phi]: bit (p-1) = ether column j0+p at phase phi, p = 1..64
typedef struct { uint64_t a[MAXW]; int nw; } Row;
static inline void step(Row *r, int c) {
    int nw = r->nw;
    if ((r->a[nw - 1] >> 62) != 0) { r->a[nw] = 0; nw = ++r->nw; }
    uint64_t prev_hi = 0;
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
// returns k of a matching family member, or -1
static int member(const Row *r, int psi) {
    uint64_t strip = (r->a[0] >> 1) | (r->nw > 1 ? (r->a[1] << 63) : 0); // columns 1..64
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
    if (fread(WALL, 1, N, f) != N) { fprintf(stderr, "bad wall file\n"); return 1; } fclose(f);
    if (P != 4) { fprintf(stderr, "driver must have length 4 (repeat shorter words)\n"); return 1; }
    for (int j = 0; j < 7; j++) for (int s = 0; s < 4; s++) {
        int ok = 1; for (int ph = 0; ph < 4; ph++) if (E[j][ph] != W[((ph - s) % 4 + 4) % 4]) ok = 0;
        if (ok) { al_j[nal] = j; al_s[nal] = s; nal++; }
    }
    for (int j = 0; j < 7; j++) for (int ph = 0; ph < 4; ph++) { uint64_t m = 0; for (int p = 1; p <= 64; p++) if (E[(j + p) % 7][ph] == '1') m |= 1ULL << (p - 1); erow[j][ph] = m; }
    printf("w=%s alignments:", W); for (int a = 0; a < nal; a++) printf(" (j0=%d,s=%d)", al_j[a], al_s[a]); printf("\n");
    const char *mode = argv[4]; long S = atol(argv[6]);
    if (!strcmp(mode, "climb")) {
        int n = atoi(argv[5]); long iters = atol(argv[7]); int ph0 = atoi(argv[8]); uint64_t rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[9]);
        #define RND() (rs ^= rs << 13, rs ^= rs >> 7, rs ^= rs << 17, rs)
        uint8_t *d = malloc(n), *best = malloc(n); static Row rr;
        long bestv = -2;
        for (long it = 0; it <= iters; it++) {
            if (it == 0) { for (int i = 0; i < n; i++) d[i] = RND() & 1; }
            else { memcpy(d, best, n); int kk = 1 + (int)(RND() % 4); for (int j = 0; j < kk; j++) d[RND() % n] ^= 1; }
            memset(rr.a, 0, sizeof(uint64_t) * (n / 64 + 8)); rr.nw = 1; rr.a[0] = d[0];
            for (int t = 0; t < n; t++) step(&rr, (t + 1 < n) ? d[t + 1] : (W[ph0] - '0'));
            long e = -1;
            for (long s2 = 0; s2 <= S; s2++) { if (member(&rr, (int)((ph0 + s2) % P)) >= 0) { e = s2; break; } step(&rr, W[(ph0 + s2 + 1) % P] - '0'); }
            if (e < 0) e = S + 1;
            if (e >= bestv) { bestv = e; memcpy(best, d, n); }
        }
        printf("w=%s n=%d ph0=%d best entry delay %ld (horizon %ld)\n", W, n, ph0, bestv, S);
        return 0;
    }
    if (!strcmp(mode, "true2")) {
        long Ta, Tb, Ts; sscanf(argv[5], "%ld:%ld:%ld", &Ta, &Tb, &Ts);
        static uint8_t cb[1250000]; FILE *cf = fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", "rb"); if (fread(cb, 1, 1250000, cf) != 1250000) return 1; fclose(cf);
        static Row tr, r2; memset(tr.a, 0, sizeof tr.a); tr.nw = 1; tr.a[0] = 1; // time 0: c(0)=1, right half empty
        long t = 0; long maxe = -1, nf = 0, tot = 0; long kh[64] = {0}; long hist[40] = {0};
        int keepw = (int)((S + 192) / 64 + 2);
        for (long T = Ta; T <= Tb; T += Ts) {
            while (t < T) { t++; step(&tr, (cb[t >> 3] >> (7 - (t & 7))) & 1); if (tr.nw >= MAXW - 2) { fprintf(stderr, "overflow true\n"); return 1; } }
            for (int ph0 = 0; ph0 < P; ph0++) {
                int nwk = tr.nw < keepw ? tr.nw : keepw;
                memcpy(r2.a, tr.a, sizeof(uint64_t) * nwk); r2.nw = nwk;
                if (nwk == keepw) r2.a[nwk - 1] = 0; // truncate (light cone keeps columns 1..64 exact for S steps)
                r2.a[0] = (r2.a[0] & ~1ULL) | (uint64_t)(W[ph0] - '0');
                long e = -1; int kk = -1;
                for (long s2 = 0; s2 <= S; s2++) {
                    int k = member(&r2, (int)((ph0 + s2) % P));
                    if (k >= 0) { e = s2; kk = k; break; }
                    step(&r2, W[(ph0 + s2 + 1) % P] - '0');
                    if (r2.nw >= MAXW - 2) { fprintf(stderr, "overflow\n"); return 1; }
                }
                tot++;
                if (e < 0) { nf++; if (nf <= 5) printf("no entry within %ld: T=%ld ph0=%d\n", S, T, ph0); }
                else { if (e > maxe) maxe = e; kh[kk]++; int bk = 0; long x = e; while (x) { bk++; x >>= 1; } hist[bk]++; }
            }
        }
        printf("w=%s bw=%d true T=%ld..%ld step %ld: runs=%ld fails=%ld max entry=%ld log2hist:", W, bw, Ta, Tb, Ts, tot, nf, maxe);
        for (int i = 0; i < 40; i++) if (hist[i]) printf(" [%d]%ld", i, hist[i]);
        printf("  k:"); for (int i = 0; i < 64; i++) if (kh[i]) printf(" %d:%ld", i, kh[i]);
        printf("\n");
        return 0;
    }
    static Row r; long maxe = -1, nfail = 0, total = 0; long hist[40] = {0}; long khist[64] = {0};
    static uint8_t cbits[1250000]; long Ta = 0, Tb = 0, Ts = 1; int n = 0; long nruns;
    int truemode = !strcmp(mode, "true");
    if (truemode) { sscanf(argv[5], "%ld:%ld:%ld", &Ta, &Tb, &Ts); FILE *cf = fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", "rb"); if (fread(cbits, 1, 1250000, cf) != 1250000) return 1; fclose(cf); nruns = (Tb - Ta) / Ts + 1; }
    else { n = atoi(argv[5]); nruns = 1L << n; }
    for (long id = 0; id < nruns; id++) {
        long nn = truemode ? Ta + id * Ts : n;
        for (int ph0 = 0; ph0 < P; ph0++) {
            memset(r.a, 0, sizeof(uint64_t) * (nn / 64 + 8)); r.nw = 1;
            #define DB(t) (truemode ? (int)((cbits[(t) >> 3] >> (7 - ((t) & 7))) & 1) : (int)((id >> (t)) & 1))
            r.a[0] = nn > 0 ? (uint64_t)DB(0) : (uint64_t)(W[ph0] - '0');
            for (long t = 0; t < nn; t++) step(&r, (t + 1 < nn) ? DB(t + 1) : (W[ph0] - '0'));
            long e = -1; int kk = -1;
            for (long s2 = 0; s2 <= S; s2++) {
                int psi = (int)((ph0 + s2) % P);
                int k = member(&r, psi);
                if (k >= 0) { e = s2; kk = k; break; }
                step(&r, W[(ph0 + s2 + 1) % P] - '0');
                if (r.nw >= MAXW - 2) { fprintf(stderr, "overflow\n"); return 1; }
            }
            total++;
            if (e < 0) { nfail++; if (nfail <= 5) printf("no entry within %ld: id=%ld (n=%ld) ph0=%d\n", S, id, nn, ph0); }
            else { if (e > maxe) maxe = e; int bk = 0; long x = e; while (x) { bk++; x >>= 1; } hist[bk]++; khist[kk]++; }
        }
    }
    printf("w=%s bw=%d %s runs=%ld fails=%ld max entry=%ld log2hist:", W, bw, mode, total, nfail, maxe);
    for (int i = 0; i < 40; i++) if (hist[i]) printf(" [%d]%ld", i, hist[i]);
    printf("  k:"); for (int i = 0; i < 64; i++) if (khist[i]) printf(" %d:%ld", i, khist[i]);
    printf("\n");
    return 0;
}
