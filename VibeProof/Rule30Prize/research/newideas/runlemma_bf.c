// Brute-force check of the "1-run lemma": in any rule-30 evolution, if column 0 is black at times
// 0..K-1 then column 1 at time K is white (K=9), and (col1|col2) at time K is 1 for K=8.
// Row at time 0 on positions [-K, K+2] (width 2K+3); each step shrinks the known window by 1 on each side.
#include <stdio.h>
#include <stdint.h>
int main(void) {
    for (int K = 7; K <= 10; K++) {
        int lo = -K, hi = K + 2, n = hi - lo + 1;   // positions lo..hi
        long cnt = 0, viol1 = 0, viol12 = 0;
        for (uint64_t x = 0; x < (1ULL << n); x++) {
            // cells as bits: bit i <-> position lo + i
            uint64_t row = x; int curlo = lo, curn = n; int ok = 1;
            for (int t = 0; t < K; t++) {
                int c0 = (row >> (0 - curlo)) & 1;
                if (!c0) { ok = 0; break; }
                // step: new cell at position p (curlo+1 .. curlo+curn-2): row[p-1] ^ (row[p] | row[p+1])
                uint64_t L = row, C = row >> 1, R = row >> 2;
                uint64_t nr = (L ^ (C | R)) & ((1ULL << (curn - 2)) - 1);
                row = nr; curlo += 1; curn -= 2;
            }
            if (!ok) continue;
            cnt++;
            int c1 = (row >> (1 - curlo)) & 1, c2 = (row >> (2 - curlo)) & 1;
            if (c1) viol1++;
            if (!(c1 | c2)) viol12++;
        }
        printf("K=%d: rows with col0=1 on [0,K): %ld; col1(K)=1 in %ld of them; col1(K)|col2(K)=0 in %ld\n", K, cnt, viol1, viol12);
    }
    return 0;
}
