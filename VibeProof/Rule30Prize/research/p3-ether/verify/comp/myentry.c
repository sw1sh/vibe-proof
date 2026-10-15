// Verifier: exact (no truncation) simulation of the right half driven by w^inf, written independently.
// Row bit i = column i+1; column 0 = driver w[(ph0 + t) % 3]; the row grows by one column per step.
// Entry: (columns 1..47 at time t, (ph0 + t) % 3) is a (state, label % 3) pair of t001.
// Modes:
//   myentry 001 trapfile supp ph0 xlo xhi H        x in [xlo, xhi) (bit i = column i+1)
//   myentry 001 trapfile list file H               lines "x ph0"
//   myentry 001 trapfile true file H               lines "T ph0": x = true rule-30 row at time T, columns 1..T
//   myentry 011 - per supp ph0 xlo xhi H PMAX      no trap; test column 1 at white times for eventual periodicity
//   myentry 011 - per true file H PMAX
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXW 16384
static uint64_t A[MAXW], B[MAXW];
static uint64_t *hk; static uint8_t *hu; static size_t hc = 0;
static size_t hf(uint64_t k) { k ^= k >> 31; k *= 0x9E3779B97F4A7C15ULL; k ^= k >> 29; k *= 0xBF58476D1CE4E5B9ULL; k ^= k >> 32; return (size_t)k & (hc - 1); }
static void hput(uint64_t k) { size_t i = hf(k); while (hu[i]) { if (hk[i] == k) return; i = (i + 1) & (hc - 1); } hu[i] = 1; hk[i] = k; }
static int hget(uint64_t k) { size_t i = hf(k); while (hu[i]) { if (hk[i] == k) return 1; i = (i + 1) & (hc - 1); } return 0; }
static int Wd[3]; static const uint64_t TMASK = (1ULL << 47) - 1;
static uint8_t *seq;
// run from A[0..nw) (higher words zero); returns entry time or -1 (no trap / not entered by H); *L = #white samples
static long run(int nw, int ph0, long H, long *L) {
    long ns = 0;
    for (long t = 0;; t++) {
        int ph = (int)((ph0 + t) % 3);
        if (hc && hget(((A[0] & TMASK) << 2) | (uint64_t)ph)) { *L = ns; return t; }
        if (t == H) break;
        int c = Wd[ph];
        if (!c) seq[ns++] = (uint8_t)(A[0] & 1);
        int nn = nw + 1; if (nn > MAXW) { fprintf(stderr, "too wide\n"); exit(1); }
        A[nw] = 0;
        uint64_t carry = (uint64_t)c;
        for (int j = 0; j < nn; j++) {
            uint64_t x = A[j], left = (x << 1) | carry, right = (x >> 1) | (j + 1 < nn ? A[j + 1] << 63 : 0);
            carry = x >> 63; B[j] = left ^ (x | right);
        }
        int k = nn; while (k > 1 && B[k - 1] == 0) k--;
        memcpy(A, B, 8 * (size_t)k); nw = k;
    }
    *L = ns; return -1;
}
// smallest p <= PMAX with seq[i] == seq[i+p] on the last half (needs 4p <= L/2), else 0
static long period(long L, long PMAX) {
    for (long p = 1; p <= PMAX && 4 * p <= L / 2; p++) {
        int ok = 1; for (long i = L / 2; i + p < L; i++) if (seq[i] != seq[i + p]) { ok = 0; break; }
        if (ok) return p;
    }
    return 0;
}
static const long TH[] = {4096, 8192, 16384, 32768, 40000, 120000, 200000, 300000};
static long nrun = 0, nent = 0, emax = -1, cum[8], nper = 0; static char argmax[64];
static void rec(long e, const char *id) {
    nrun++;
    if (e >= 0) { nent++; if (e > emax) { emax = e; snprintf(argmax, sizeof argmax, "%s", id); } for (int i = 0; i < 8; i++) if (e <= TH[i]) cum[i]++; }
}
static void report(void) {
    printf("runs %ld entered %ld (%.3f%%) max entry %ld at [%s]; not entered %ld; col1@white periodic (non-entered) %ld\n",
           nrun, nent, 100.0 * nent / (nrun ? nrun : 1), emax, argmax, nrun - nent, nper);
    printf("  cumulative entry <= 4096:%ld 8192:%ld 16384:%ld 32768:%ld 40000:%ld 120000:%ld 200000:%ld 300000:%ld\n",
           cum[0], cum[1], cum[2], cum[3], cum[4], cum[5], cum[6], cum[7]);
}
// true pattern: positions -Tm-2..Tm+2 at offset OFF
static uint64_t *P0, *P1; static long OFF, PNW;
static void pstep(void) {
    uint64_t carry = 0;
    for (long j = 0; j < PNW; j++) { uint64_t x = P0[j], left = (x << 1) | carry, right = (x >> 1) | (j + 1 < PNW ? P0[j + 1] << 63 : 0); carry = x >> 63; P1[j] = left ^ (x | right); }
    uint64_t *tmp = P0; P0 = P1; P1 = tmp;
}
static int pget(long p) { long i = p + OFF; return (int)((P0[i >> 6] >> (i & 63)) & 1); }
int main(int argc, char **argv) {
    for (int i = 0; i < 3; i++) Wd[i] = argv[1][i] - '0';
    if (strcmp(argv[2], "-")) {
        FILE *f = fopen(argv[2], "r"); long n; int b; if (fscanf(f, "%ld %d", &n, &b) != 2 || b != 47) return 1;
        hc = 1; while (hc < 8 * (size_t)n) hc <<= 1; hk = calloc(hc, 8); hu = calloc(hc, 1);
        for (long i = 0; i < n; i++) { unsigned long long s; int l; if (fscanf(f, "%llu %d", &s, &l) != 2) return 1; hput(((uint64_t)s << 2) | (uint64_t)(l % 3)); }
        fclose(f);
    }
    int a = 3; int per = 0; if (!strcmp(argv[a], "per")) { per = 1; a++; }
    const char *mode = argv[a];
    seq = malloc(1 << 22);
    char id[64];
    if (!strcmp(mode, "supp")) {
        int ph0 = atoi(argv[a + 1]); long xlo = atol(argv[a + 2]), xhi = atol(argv[a + 3]), H = atol(argv[a + 4]);
        long PMAX = per ? atol(argv[a + 5]) : 0;
        for (long x = xlo; x < xhi; x++) {
            memset(A, 0, 16); A[0] = (uint64_t)x; long L;
            long e = run(1, ph0, H, &L); snprintf(id, sizeof id, "%ld %d", x, ph0); rec(e, id);
            if (e < 0) { long p = period(L, per ? PMAX : 2499); if (p) { nper++; if (nper <= 5) printf("  periodic: x=%ld ph0=%d p=%ld samples\n", x, ph0, p); } }
        }
        report(); return 0;
    }
    if (!strcmp(mode, "rand")) {   // rand ph0 count seed H [PMAX]: x = 64 random bits (columns 1..64), splitmix64
        int ph0 = atoi(argv[a + 1]); long cntr = atol(argv[a + 2]); uint64_t st = (uint64_t)atol(argv[a + 3]); long H = atol(argv[a + 4]);
        long PMAX = per ? atol(argv[a + 5]) : 2499;
        for (long k = 0; k < cntr; k++) {
            st += 0x9E3779B97F4A7C15ULL; uint64_t z = st; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; z ^= z >> 31;
            memset(A, 0, 16); A[0] = z; long L;
            long e = run(2, ph0, H, &L); snprintf(id, sizeof id, "rand%ld %d", k, ph0); rec(e, id);
            if (e < 0) { long p = period(L, PMAX); if (p) nper++; }
        }
        report(); return 0;
    }
    if (!strcmp(mode, "list")) {
        FILE *lf = fopen(argv[a + 1], "r"); long H = atol(argv[a + 2]); unsigned long long x; int ph0;
        while (fscanf(lf, "%llu %d", &x, &ph0) == 2) {
            memset(A, 0, 16); A[0] = (uint64_t)x; long L;
            long e = run(1, ph0, H, &L); snprintf(id, sizeof id, "%llu %d", x, ph0); rec(e, id);
            printf("  x=%llu ph0=%d entry=%ld\n", x, ph0, e);
        }
        report(); return 0;
    }
    if (!strcmp(mode, "true")) {
        FILE *lf = fopen(argv[a + 1], "r"); long H = atol(argv[a + 2]); long PMAX = per ? atol(argv[a + 3]) : 2499;
        static long LT[100000]; static int LP[100000]; long nl = 0, Tm = 0;
        while (nl < 100000 && fscanf(lf, "%ld %d", &LT[nl], &LP[nl]) == 2) { if (LT[nl] > Tm) Tm = LT[nl]; nl++; }
        OFF = Tm + 128; PNW = (2 * Tm + 256) / 64 + 2; P0 = calloc(PNW, 8); P1 = calloc(PNW, 8);
        P0[OFF >> 6] |= 1ULL << (OFF & 63);
        FILE *cf = fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", "rb");
        static uint8_t cb[1250000]; if (!cf || fread(cb, 1, 1250000, cf) != 1250000) { fprintf(stderr, "center file\n"); return 1; } fclose(cf);
        long mism = 0;
        for (long T = 0; T <= Tm; T++) {
            if (pget(0) != ((cb[T >> 3] >> (7 - (T & 7))) & 1)) mism++;
            for (long k = 0; k < nl; k++) if (LT[k] == T) {
                long nw = T / 64 + 2; if (nw > MAXW) { fprintf(stderr, "too wide\n"); return 1; }
                memset(A, 0, 8 * (size_t)(nw + 1));
                for (long p = 1; p <= T; p++) if (pget(p)) A[(p - 1) >> 6] |= 1ULL << ((p - 1) & 63);
                long L; long e = run((int)nw, LP[k], H, &L); snprintf(id, sizeof id, "T=%ld ph0=%d", T, LP[k]); rec(e, id);
                if (e < 0) { long p = period(L, PMAX); if (p) nper++; }
                if (!per) printf("  T=%ld ph0=%d entry=%ld\n", T, LP[k], e);
            }
            pstep();
        }
        printf("center column vs center-1e7.bin, t = 0..%ld: %ld mismatches\n", Tm, mism);
        report(); return 0;
    }
    return 1;
}
