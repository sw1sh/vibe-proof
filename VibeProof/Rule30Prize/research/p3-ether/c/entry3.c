// Period-3 empirics: the right half driven by w^inf (w = 001 or 011).
// For each run (initial right half x, driver phase ph0): simulate S steps; detect entry into a labelled trap
// (strip of columns 1..b with phase = label % 3) and test whether column 1 at the white times of the driver is
// eventually periodic (smallest period <= PMAX samples holding on the last half with >= 4 repetitions).
// Modes:
//   entry3 w trapfile|- S PMAX supp n          all x with support in [1,n] (2^n halves), all 3 phases
//   entry3 w trapfile|- S PMAX true Ta Tb Ts   true rule-30 right halves at T = Ta, Ta+Ts, ..., Tb, all 3 phases
//   entry3 w trapfile|- S PMAX rand n cnt seed random halves with support in [1,n], cnt of them, all 3 phases
// The true right halves come from a direct simulation of the single-seed pattern; its center column is
// compared with center-1e7.bin (read-only) as a cross-check.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static const char *W; static int P;
static int tb = 0, tm = 0; static long tn = 0; // trap width, label modulus, #states
static uint64_t *hkey; static uint8_t *hused; static size_t hcap;
static size_t hh(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return (size_t)k & (hcap - 1); }
static void hput(uint64_t k) { size_t i = hh(k); while (hused[i]) { if (hkey[i] == k) return; i = (i + 1) & (hcap - 1); } hused[i] = 1; hkey[i] = k; }
static int hget(uint64_t k) { size_t i = hh(k); while (hused[i]) { if (hkey[i] == k) return 1; i = (i + 1) & (hcap - 1); } return 0; }
#define MAXWD 16384
static uint64_t row[MAXWD], nwr[MAXWD];
static inline void step(int nwords, int c) {
    uint64_t carry = (uint64_t)c;
    for (int j = 0; j < nwords; j++) {
        uint64_t x = row[j], left = (x << 1) | carry, right = (x >> 1) | (j + 1 < nwords ? row[j + 1] << 63 : 0);
        carry = x >> 63; nwr[j] = left ^ (x | right);
    }
    memcpy(row, nwr, 8 * (size_t)nwords);
}
static int S, PMAX; static uint8_t *seq;
// statistics
static long runs = 0, entered = 0, maxentry = -1, perN = 0, aperN = 0; static double sumentry = 0;
static long ehist[40], perhist[4096]; static long maxonset = -1;
static long ent_by_phase[3], runs_by_phase[3];
// run from the current row[] (columns 1..), driver phase ph0; returns entry time or -1
static long run_one(int ph0, int nwords0, long *perout, long *onsetout) {
    int L = 0; long e = -1; int nwords = nwords0;
    uint64_t mask = tb ? (tb == 64 ? ~0ULL : ((1ULL << tb) - 1)) : 0;
    for (int t = 0; t <= S; t++) {
        int ph = (ph0 + t) % P;
        if (tb && hget(((row[0] & mask) << 2) | (uint64_t)ph)) { e = t; break; }
        if (t == S) break;
        int c = W[ph] - '0';
        if (!c) seq[L++] = (uint8_t)(row[0] & 1);
        int need = (tb + (S - t) + 2) / 64 + 2; if (need < nwords) nwords = need;
        step(nwords, c);
    }
    *perout = 0; *onsetout = -1;
    if (e < 0) {
        for (int p = 1; p <= PMAX && 4 * p <= L / 2; p++) {
            int ok = 1; for (int i = L / 2; i + p < L; i++) if (seq[i] != seq[i + p]) { ok = 0; break; }
            if (ok) { int onset = L - p; while (onset > 0 && seq[onset - 1] == seq[onset - 1 + p]) onset--; *perout = p; *onsetout = onset; break; }
        }
    }
    return e;
}
static void record(int ph0, long e, long per, long onset) {
    runs++; runs_by_phase[ph0]++;
    if (e >= 0) { entered++; ent_by_phase[ph0]++; sumentry += (double)e; if (e > maxentry) maxentry = e; int bk = 0; long x = e; while (x) { bk++; x >>= 1; } ehist[bk]++; }
    else if (per) { perN++; long st = per * P / 2; (void)st; if (per < 4096) perhist[per]++; if (onset > maxonset) maxonset = onset; }
    else aperN++;
}
static void report(const char *tag) {
    int nwhite = 0; for (int i = 0; i < P; i++) if (W[i] == '0') nwhite++;
    printf("w=%s %s S=%d: runs %ld | trap entries %ld (%.2f%%), max delay %ld, mean delay %.1f | not entered: col1@white eventually periodic %ld, aperiodic %ld\n",
           W, tag, S, runs, entered, 100.0 * entered / (runs ? runs : 1), maxentry, entered ? sumentry / entered : 0.0, perN, aperN);
    printf("  entries by phase: %ld/%ld %ld/%ld %ld/%ld", ent_by_phase[0], runs_by_phase[0], ent_by_phase[1], runs_by_phase[1], ent_by_phase[2], runs_by_phase[2]);
    printf("  | entry-delay log2 histogram:"); for (int i = 0; i < 40; i++) if (ehist[i]) printf(" [%d]%ld", i, ehist[i]);
    printf("\n  periodic-but-not-entered periods (white samples -> steps):");
    for (int p = 1; p < 4096; p++) if (perhist[p]) printf(" %d->%d:%ld", p, p * P / nwhite, perhist[p]);
    if (perN) printf("  max onset %ld samples", maxonset);
    printf("\n");
}
int main(int argc, char **argv) {
    W = argv[1]; P = (int)strlen(W); S = atoi(argv[3]); PMAX = atoi(argv[4]); const char *mode = argv[5];
    seq = malloc((size_t)S + 8);
    if (strcmp(argv[2], "-")) {
        FILE *f = fopen(argv[2], "r"); char ww[16]; if (fscanf(f, "%15s %d %d %ld", ww, &tb, &tm, &tn) != 4) return 1;
        if (strcmp(ww, W) || tb > 62) { fprintf(stderr, "trap word/width mismatch\n"); return 1; }
        hcap = 1; while (hcap < 4 * (size_t)tn + 16) hcap <<= 1; hkey = calloc(hcap, 8); hused = calloc(hcap, 1);
        for (long i = 0; i < tn; i++) { unsigned long long r; int l; if (fscanf(f, "%llu %d", &r, &l) != 2) return 1; hput(((uint64_t)r << 2) | (uint64_t)(l % 3)); }
        fclose(f);
    }
    int nwords0 = (tb + S + 2) / 64 + 3; if (nwords0 > MAXWD) { fprintf(stderr, "too wide\n"); return 1; }
    if (!strcmp(mode, "list")) {
        FILE *lf = fopen(argv[6], "r"); unsigned long long xv; int ph0; long cntl = 0;
        FILE *sf = argc > 7 ? fopen(argv[7], "w") : NULL;
        while (fscanf(lf, "%llu %d", &xv, &ph0) == 2) {
            memset(row, 0, 8 * (size_t)nwords0); row[0] = (uint64_t)xv;
            long per, onset; long e = run_one(ph0, nwords0, &per, &onset); record(ph0, e, per, onset); cntl++;
            if (e < 0 && sf) fprintf(sf, "%llu %d\n", xv, ph0);
        }
        fclose(lf); if (sf) fclose(sf);
        report("list"); return 0;
    }
    if (!strcmp(mode, "supp") || !strcmp(mode, "rand")) {
        int n = atoi(argv[6]); long cnt = !strcmp(mode, "rand") ? atol(argv[7]) : (1L << n);
        uint64_t rs = !strcmp(mode, "rand") ? (0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[8])) : 0;
        long start = 0, stride = 1; FILE *sf = NULL;
        if (!strcmp(mode, "supp") && argc > 8) { start = atol(argv[7]); stride = atol(argv[8]); }
        if (!strcmp(mode, "supp") && argc > 9) sf = fopen(argv[9], "w");
        for (long id = start; id < cnt; id += stride) {
            uint64_t xw[4] = {0, 0, 0, 0};
            if (!strcmp(mode, "rand")) { for (int k = 0; k < (n + 63) / 64; k++) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; xw[k] = rs; }
                if (n % 64) xw[(n - 1) / 64] &= (1ULL << (n % 64)) - 1; }
            else xw[0] = (uint64_t)id;
            for (int ph0 = 0; ph0 < P; ph0++) {
                memset(row, 0, 8 * (size_t)nwords0); for (int k = 0; k < 4 && k < nwords0; k++) row[k] = xw[k];
                long per, onset; long e = run_one(ph0, nwords0, &per, &onset); record(ph0, e, per, onset);
                if (e < 0 && sf) fprintf(sf, "%llu %d\n", (unsigned long long)xw[0], ph0);
            }
        }
        if (sf) fclose(sf);
        char tag[96]; snprintf(tag, sizeof tag, "%s n=%d start=%ld stride=%ld", mode, n, start, stride); report(tag);
        return 0;
    }
    if (!strcmp(mode, "true") || !strcmp(mode, "truelist")) {
        int islist = !strcmp(mode, "truelist");
        long Ta = 0, Tb = 0, Ts = 1; FILE *sf = NULL;
        static long LT[200000]; static int LP[200000]; long nl = 0, li = 0;
        if (islist) { FILE *lf = fopen(argv[6], "r"); while (nl < 200000 && fscanf(lf, "%ld %d", &LT[nl], &LP[nl]) == 2) { if (LT[nl] > Tb) Tb = LT[nl]; nl++; } fclose(lf);
                      if (argc > 7) sf = fopen(argv[7], "w"); }
        else { Ta = atol(argv[6]); Tb = atol(argv[7]); Ts = atol(argv[8]); if (argc > 9) sf = fopen(argv[9], "w"); }
        // full single-seed pattern, positions -Tb-1 .. Tb+1; bit index i = p + OFF
        long OFF = Tb + 64; long NB = 2 * Tb + 192; int NW = (int)(NB / 64 + 2);
        uint64_t *A = calloc((size_t)NW, 8), *B = calloc((size_t)NW, 8);
        A[OFF / 64] |= 1ULL << (OFF % 64);
        static uint8_t cb[1250000]; FILE *cf = fopen("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", "rb");
        if (!cf || fread(cb, 1, 1250000, cf) != 1250000) { fprintf(stderr, "center file\n"); return 1; } fclose(cf);
        long mism = 0;
        for (long T = 0; T <= Tb; T++) {
            int cbit = (int)((A[OFF / 64] >> (OFF % 64)) & 1);
            if (cbit != ((cb[T >> 3] >> (7 - (T & 7))) & 1)) mism++;
            for (int ph0 = 0; ph0 < P; ph0++) {
                int doit = islist ? 0 : (T >= Ta && (T - Ta) % Ts == 0);
                if (islist) { for (long k = 0; k < nl; k++) if (LT[k] == T && LP[k] == ph0) { doit = 1; break; } }
                if (!doit) continue;
                memset(row, 0, 8 * (size_t)nwords0);
                // columns 1..min(T, 64*nwords0) of the true row at time T
                for (long p = 1; p <= T && p <= 64L * nwords0; p++) { long i = p + OFF; if ((A[i / 64] >> (i % 64)) & 1) row[(p - 1) / 64] |= 1ULL << ((p - 1) % 64); }
                long per, onset; long e = run_one(ph0, nwords0, &per, &onset); record(ph0, e, per, onset);
                if (e < 0 && sf) fprintf(sf, "%ld %d\n", T, ph0);
            }
            // step the full pattern
            uint64_t carry = 0;
            for (int j = 0; j < NW; j++) { uint64_t x = A[j], left = (x << 1) | carry, right = (x >> 1) | (j + 1 < NW ? A[j + 1] << 63 : 0); carry = x >> 63; B[j] = left ^ (x | right); }
            uint64_t *tmp = A; A = B; B = tmp;
        }
        if (sf) fclose(sf); (void)li;
        char tag[128]; snprintf(tag, sizeof tag, "%s T=%ld..%ld step %ld (center mismatches vs file: %ld)", mode, Ta, Tb, Ts, mism); report(tag);
        return 0;
    }
    fprintf(stderr, "unknown mode\n"); return 1;
}
