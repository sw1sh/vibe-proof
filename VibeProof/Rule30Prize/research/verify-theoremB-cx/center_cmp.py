import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
from real_pattern_check import evolve_full_int
steps = 3000
W = 2 * steps + 5
mid = steps + 2
rows = evolve_full_int(1 << mid, W, steps)
center = [(rows[t] >> mid) & 1 for t in range(steps + 1)]
brief = [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1]
print("brief 20 match:", center[:20] == brief)
data = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb').read(400)
bits = []
for byte in data:
    for k in range(7, -1, -1):
        bits.append((byte >> k) & 1)
print("data file match first 3000:", bits[:3001] == center[:3001], len(bits))
