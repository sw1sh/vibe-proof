// Like dfs.c but prints the configs (L(1..W)) and column-1 prefixes reaching depth >= thr.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int W, MAXD, THR;
static int Lbits[300], xbits[300];
static u128 suffix_xor(u128 b) { b ^= b >> 1; b ^= b >> 2; b ^= b >> 4; b ^= b >> 8; b ^= b >> 16; b ^= b >> 32; b ^= b >> 64; return b; }
static int deepest;
static void dfs(int m, u128 Am1, u128 Am) {
  if (m > deepest) deepest = m;
  if (m >= THR) {
    // check that this is a maximal extension: print at the end of the path
  }
  u128 mask = (m >= 1) ? ((((u128)1) << m) - 1) : 0;
  u128 B = (Am | Am1) & mask;
  u128 S = suffix_xor(B) & mask;
  int ext = 0;
  if (m < MAXD)
  for (int xb = 0; xb <= 1; xb++) {
    if ((m & 1) == 0 && xb == 0) continue;
    u128 An = (xb ? mask : 0) ^ S;
    if (xb) An |= (((u128)1) << m);
    if (m + 1 > W && (An & 1)) continue;
    Lbits[m + 1] = (int)(An & 1); xbits[m] = xb;
    ext = 1;
    dfs(m + 1, Am, An);
  }
  if (!ext && m >= THR) {
    printf("W=%d depth=%d L=", W, m);
    for (int k = 1; k <= W; k++) putchar(Lbits[k] ? '1' : '0');
    printf(" x1=");
    for (int t = 0; t < m; t++) putchar(xbits[t] ? '1' : '0');
    printf("\n");
  }
}
int main(int argc, char **argv) {
  W = atoi(argv[1]); THR = atoi(argv[2]); MAXD = argc > 3 ? atoi(argv[3]) : 125;
  deepest = 0;
  dfs(0, 0, 0);
  printf("deepest %d\n", deepest);
}
