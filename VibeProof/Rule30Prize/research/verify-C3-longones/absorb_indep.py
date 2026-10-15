# Independent check of C2 ("absorption"): if the center column is 1 at times s-9..s-1,
# then cell(s,1)=0 and cell(s,2)=1, for EVERY possible right-half state at time s-9.
# Written from scratch (does not reuse the Lean helpers or other agents' scripts).
import itertools, random

def r30(l, c, r):
    return l ^ (c | r)

def drive(right, drivers):
    # right: list of bits for positions 1..W at the starting time (beyond W: treated as unknown,
    # so we shrink the valid window by one per step). drivers: center values c(start), c(start+1), ...
    row = list(right)
    for c in drivers:
        full = [c] + row          # full[0] = position 0, full[p] = position p
        row = [r30(full[p-1], full[p], full[p+1]) for p in range(1, len(full)-1)]
    return row                    # valid positions 1..W-len(drivers)

def min_steps_needed(maxk=12):
    # smallest k such that k ones force (cell1,cell2) = (0,1) for all states
    for k in range(1, maxk+1):
        W = k + 2
        outs = set()
        for bits in itertools.product((0,1), repeat=W):
            out = drive(bits, [1]*k)
            outs.add(tuple(out[:2]))
        print(f"k={k}: reachable (cell1,cell2) after k ones from all 2^{W} states: {sorted(outs)}")
        if outs == {(0,1)}:
            return k
    return None

k = min_steps_needed()
print("minimal number of consecutive ones forcing (0,1):", k)

# Exhaustive check at exactly 9 steps over positions 1..11 (2^11 states), plus a
# light-cone sanity check: padding with random bits beyond position 11 must not matter.
bad = 0
for bits in itertools.product((0,1), repeat=11):
    out = drive(bits, [1]*9)
    if tuple(out[:2]) != (0,1):
        bad += 1
    for _ in range(3):
        pad = [random.randint(0,1) for _ in range(20)]
        out2 = drive(list(bits)+pad, [1]*9)
        assert tuple(out2[:2]) == tuple(out[:2])
print("9 ones, 2^11 states: failures =", bad)

# Also: once (0,1) and center stays 1, it stays (0,1)? (not needed by the proof, just a check)
