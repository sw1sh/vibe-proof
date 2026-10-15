# For each word w and several random right-half start states (width T, right edge at +T), drive the right
# half with c(t) = w[(t) mod P] and test: is column 1 eventually periodic?  is column 1 restricted to
# Z = {t: c(t)=0} eventually periodic (period multiple of P)?
import sys, random
def run_right(state, T, w, steps):
    P = len(w); row = state; col = []
    for k in range(steps):
        t = T + k
        col.append(row & 1)
        W = t + 1; mask = (1 << W) - 1
        leftn = ((row << 1) | int(w[k % P])) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return col
def ev_period(seq, okidx, P0, maxmult=64):
    n = len(seq)
    for m in range(1, maxmult + 1):
        P = m * P0
        bad = [k for k in range(n - P) if okidx(k) and seq[k] != seq[k + P]]
        T = (bad[-1] + 1) if bad else 0
        if T <= n // 2: return (T, P)
    return None
def main():
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    words = sys.argv[2:]
    for w in words:
        P = len(w); stats = {'full': 0, 'Zonly': 0, 'neither': 0}
        for trial in range(12):
            T = random.randint(5, 60)
            state = random.getrandbits(T - 1) | (1 << (T - 1))   # bit i <-> p = i+1; rightmost black at p = T
            col = run_right(state, T, w, 2400)
            full = ev_period(col, lambda k: True, P)
            onZ = ev_period(col, lambda k: w[k % P] == '0', P)
            if full: stats['full'] += 1
            elif onZ: stats['Zonly'] += 1
            else: stats['neither'] += 1
        print(w, stats)
if __name__ == "__main__":
    main()
