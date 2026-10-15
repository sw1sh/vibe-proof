#!/usr/bin/env python3
"""Re-check (z3) whether the stored surviving-pair sets of A-invsearch/dfa_pairs_{n}_{dir}.json are UNSAT for
every n-state DFA prefix-ranking (encoding of A-invsearch/dfa_rank_sat.py)."""
import sys, json, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
import dfa_rank_sat as D
from z3 import unsat
n = int(sys.argv[1]); d = sys.argv[2]
pairs = json.load(open(f'/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch/dfa_pairs_{n}_{d}.json'))
# sanity: each stored x is a genuine surviving double step from a finite start
ok = all((x & 1) and (D.G(x) & 1) for x in pairs)
E = D.Enc(n, d)
for x in pairs: E.add_pair(x)
t = time.time(); r = E.S.check()
print(f"n={n} dir={d}: {len(pairs)} pairs, all genuine surviving pairs: {ok}; z3 says {r} ({time.time()-t:.1f}s)")
