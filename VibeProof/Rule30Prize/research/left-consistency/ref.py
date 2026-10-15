# Reference (brute force) for the left-half consistency experiment.
# Left half at time T: cells p = -1..-T, cell(T,-T) = 1, zeros beyond.  bit i <-> p = -(i+1).
# Driver c(t) = w[(t-T) mod P] for t >= T.  Forced: c(t) = 1  =>  x(t) = cell(t,-1) = 1 - c(t+1).
# Returns for each state the first violation time (or None if it survives to horizon H).
import sys

def first_violation(state, T, w, H):
    P = len(w)
    c = lambda t: int(w[(t - T) % P])
    row = state
    for t in range(T, H):
        x = row & 1
        if c(t) == 1 and x != 1 - c(t + 1):
            return t
        W = t + 1  # length of row at time t+1
        mask = (1 << W) - 1
        right = ((row << 1) | c(t)) & mask
        left = row >> 1
        row = (left ^ (row | right)) & mask
    return None

def survey(w, T, H):
    res = []
    for s in range(1 << (T - 1)):
        state = s | (1 << (T - 1))
        res.append(first_violation(state, T, w, H))
    return res

if __name__ == "__main__":
    w = sys.argv[1]; Tmax = int(sys.argv[2]); fac = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    for T in range(1, Tmax + 1):
        H = fac * T + 20
        r = survey(w, T, H)
        surv = sum(1 for v in r if v is None)
        mx = max((v for v in r if v is not None), default=None)
        print(T, "states", len(r), "survive_to_H", surv, "max_first_violation", mx, "H", H)
