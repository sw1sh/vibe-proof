// DFS with restricted free bits: f has no "00" and no run of RMAX+1 ones (zeros 2..RMAX+1 apart in index).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int W, MAXD, RMAX;
static long long cnt[256];
static int maxreach;
static u128 suffix_xor(u128 b) { b ^= b >> 1; b ^= b >> 2; b ^= b >> 4; b ^= b >> 8; b ^= b >> 16; b ^= b >> 32; b ^= b >> 64; return b; }
// lastf: previous free bit (-1 none), run: current run of ones in f
static void dfs(int m, u128 Am1, u128 Am, int lastf, int run) {
  cnt[m]++;
  if (m > maxreach) maxreach = m;
  if (m >= MAXD) return;
  u128 mask = (m >= 1) ? ((((u128)1) << m) - 1) : 0;
  u128 B = (Am | Am1) & mask;
  u128 S = suffix_xor(B) & mask;
  for (int xb = 0; xb <= 1; xb++) {
    int nl = lastf, nr = run;
    if ((m & 1) == 0) { if (xb == 0) continue; }
    else {
      if (xb == 0 && lastf == 0) continue;
      if (xb == 1 && run >= RMAX) continue;
      nl = xb; nr = xb ? run + 1 : 0;
    }
    u128 An = (xb ? mask : 0) ^ S;
    if (xb) An |= (((u128)1) << m);
    if (m + 1 > W && (An & 1)) continue;
    dfs(m + 1, Am, An, nl, nr);
  }
}
int main(int argc, char **argv) {
  int W0 = atoi(argv[1]), W1 = atoi(argv[2]); RMAX = atoi(argv[3]); MAXD = 125;
  for (W = W0; W <= W1; W++) {
    memset(cnt, 0, sizeof cnt); maxreach = 0;
    dfs(0, 0, 0, -1, 0);
    printf("W=%2d RMAX=%d maxprefix=%3d\n", W, RMAX, maxreach); fflush(stdout);
  }
}
