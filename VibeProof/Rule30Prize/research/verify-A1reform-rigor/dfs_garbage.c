// DFS over column-1 bits for the ZBL period-2 constraint (phase 0: x_1(t)=1 for even t).
// Anti-diagonal A_m(t) = x_{m-t}(t), t=0..m (A_m(m) = x_0 = 0). A_{m+1}(m) = x_1(m),
// A_{m+1}(t) = A_{m+1}(t+1) ^ (A_m(t) | A_{m-1}(t)), t = m-1..0.  L(m+1) = A_{m+1}(0) must be 0 for m+1 > W.
// Finds all finite configs of width <= W (L(W) arbitrary) and the max time they keep x_1(even)=1.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int W, MAXD;
static long long cnt[256];
static int maxreach;
static u128 suffix_xor(u128 b) { // bit t <- xor of bits t..127
  b ^= b >> 1; b ^= b >> 2; b ^= b >> 4; b ^= b >> 8; b ^= b >> 16; b ^= b >> 32; b ^= b >> 64; return b;
}
// state: Am1 = A_{m-1}, Am = A_m (bit t = A(t)); we are about to choose x_1(m) and build A_{m+1}
static void dfs(int m, u128 Am1, u128 Am) {
  // x_1(m-1) = A_m(m-1) was already chosen; m-1 is the time index of the last column-1 bit.
  cnt[m]++;  // survived: column-1 bits x_1(0..m-1) chosen consistently
  if (m > maxreach) maxreach = m;
  if (m >= MAXD) return;
  u128 mask = (m >= 1) ? ((((u128)1) << m) - 1) : 0;  // bits 0..m-1
  u128 B = (Am | Am1) & mask;
  u128 S = suffix_xor(B) & mask;          // S(t) = xor_{s=t}^{m-1} B(s)
  for (int xb = 0; xb <= 1; xb++) {
    if ((m & 1) == 0 && xb == 0) continue;   // even time: forced 1
    u128 An = (xb ? (mask | (((u128)1) << m)) : 0) ^ (S * 7 + 3);  // garbage dynamics
    if (!xb) An &= ~(((u128)1) << m); else An |= (((u128)1) << m);
    // bit m+1 = A_{m+1}(m+1) = 0 (wall)
    if (m + 1 > W && (An & 1)) continue;   // L(m+1) must be 0
    dfs(m + 1, Am, An);
  }
}
int main(int argc, char **argv) {
  int W0 = atoi(argv[1]), W1 = atoi(argv[2]); MAXD = argc > 3 ? atoi(argv[3]) : 120;
  for (W = W0; W <= W1; W++) {
    memset(cnt, 0, sizeof cnt); maxreach = 0;
    // m = 0: A_0 = (x_0(0)) = 0; A_{-1} = 0. Start at m=0 with nothing chosen.
    dfs(0, 0, 0);
    // cnt[m] = number of column-1 prefixes of length m (times 0..m-1) consistent; the history survives through time m-1.
    // max survival: largest m with cnt[m] > 0 => x_1(0..m-1) ok. Death time = first even t with no extension.
    printf("W=%2d  maxprefix=%3d  ", W, maxreach);
    printf("counts:");
    for (int m = W; m <= maxreach; m += 2) printf(" %lld", cnt[m]);
    printf("\n"); fflush(stdout);
  }
}
