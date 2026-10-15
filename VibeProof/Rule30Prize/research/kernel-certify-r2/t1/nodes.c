/* node counts of the plain anti-diagonal DFS (no dedup); 128-bit states (k <= 126) */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static u128 scan(u128 s){ s^=s>>1; s^=s>>2; s^=s>>4; s^=s>>8; s^=s>>16; s^=s>>32; s^=s>>64; return s; }
static int W; static long long nodes; static int deepest;
static long long levelnodes[200];
static void dfs(int k, u128 A, u128 B){
  if (k > 125) { printf("too deep\n"); exit(1); }
  u128 s = scan(A|B), m = (((u128)1)<<k) - 1;
  for (int b = (k%2==0) ? 1 : 0; b <= 1; b++) {
    u128 C = b ? ((s^m)|(m+1)) : s; nodes++; levelnodes[k]++;
    if (k+1 > W && (C & 1)) continue;
    if (k+1 > deepest) deepest = k+1;
    dfs(k+1, B, C);
  }
}
int main(int argc, char**argv){
  int w0 = atoi(argv[1]), w1 = atoi(argv[2]);
  for (W = w0; W <= w1; W++) { nodes = 0; deepest = 0; dfs(0,0,0);
    printf("W=%d nodes=%lld deepest=%d\n", W, nodes, deepest); fflush(stdout); }
  return 0;
}
