# Independent cross-check of trap entry times for w = 001 (exact big-int simulation, no truncation).
# The trap states are decoded from the Lean data file (packed tables R, L of t001).
import sys, re
sys.set_int_max_str_digits(0)
src = open(sys.argv[1]).read()
get = lambda nm: int(re.search(r"def t001_%s : Nat := (\d+)" % nm, src).group(1))
n, lb, R, Lt = get('n'), get('lb'), get('R'), get('L')
b, m, w = 47, 21, "001"
states = set()
for i in range(n):
    r = (R >> (b * i)) & ((1 << b) - 1); l = (Lt >> (lb * i)) & ((1 << lb) - 1)
    states.add((r, l % 3))
cases = [(int(a), int(c)) for a, c in (s.split(',') for s in sys.argv[2:])]
for (x, ph0) in cases:
    row = x  # bit i = column i+1
    t = 0; e = None
    while t <= 400000:
        ph = (ph0 + t) % 3
        if ((row & ((1 << b) - 1)), ph) in states: e = t; break
        c = int(w[ph]); full = c | (row << 1)
        row = (full ^ ((full >> 1) | (full >> 2)))
        # full has bit 0 = column 0; new columns 1.. are bits 1.. of the rule image; shift down by 1
        t += 1
    print(f"x={x} ph0={ph0}: first entry at t={e}")
