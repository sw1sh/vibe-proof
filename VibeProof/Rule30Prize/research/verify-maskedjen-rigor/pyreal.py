# Independent Python: actual single-seed rule-30 right half at time T, then driver switched to w^inf (phase ph).
# Report from when col1 is masked-|w|-periodic and full-2|w|-periodic, up to the horizon.
import sys
w = sys.argv[1]; steps = int(sys.argv[2]); Ts = range(int(sys.argv[3]), int(sys.argv[4]) + 1)
P = len(w); wb = [int(ch) for ch in w]
def pattern_row(T):
    # full row at time T as int with bit (p + T) <-> position p, p in [-T, T]
    r = 1 << T  # position 0 at bit T (after T steps, positions -T..T => offset T)
    # simulate with offset that grows: use fixed offset OFF = T
    OFF = T; row = 1 << OFF
    for s in range(T):
        row = (row << 1) ^ (row | (row >> 1))  # wrong orientation guard below
    return row
# Orientation: bit k <-> position k - OFF; left neighbour of position p is p-1 = bit k-1.
# new[k] = old[k-1] xor (old[k] or old[k+1]) => new = (old << 1) xor (old | old >> 1). Matches above.
def right_half(T):
    row = pattern_row(T)
    # positions p >= 1 <-> bits k = p + T >= T + 1 ; right-half encoding: bit i <-> position i + 1
    return row >> (T + 1)
def center(T):
    return (pattern_row(T) >> T) & 1
# sanity: center column prefix
print('c prefix:', ''.join(str(center(t)) for t in range(20)))
bad = 0; worst = (0, None)
for T in Ts:
    for ph in range(P):
        row = right_half(T); col = []
        for t in range(steps):
            col.append(row & 1)
            row = (((row << 1) | wb[(t + ph) % P]) ^ (row | (row >> 1)))
        n = len(col)
        def pf(Q, masked):
            S = n - Q
            while S > 0 and ((masked and wb[(S - 1 + ph) % P] == 1) or col[S - 1] == col[S - 1 + Q]): S -= 1
            return S
        m = pf(P, True); f8 = pf(2 * P, False)
        if m > n // 2: bad += 1; print('T', T, 'ph', ph, 'masked not periodic on 2nd half; from', m)
        worst = max(worst, (m, (T, ph)))
print(w, 'T range', Ts, 'steps', steps, 'bad', bad, 'latest masked onset', worst)
