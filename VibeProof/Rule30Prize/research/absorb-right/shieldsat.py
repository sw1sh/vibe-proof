# Shield test via SAT: sigma-driven right half; at times n == zero-phase (mod Q), is x(n,1) forced?
import sys, time
sys.path.insert(0, '.')
from satcol import possible_values
def shield_sat(sigma, nmax=60):
    Q = len(sigma); zeros = [r for r in range(Q) if sigma[r] == '0']
    res = {}
    for r in zeros:
        found = None
        for n in range(r, nmax + 1, Q):
            pv = possible_values(sigma, n)
            if len(pv) == 1: found = (pv[0], n); break
        if found is None: return None
        res[r] = found
    return res
if __name__ == '__main__':
    nmax = int(sys.argv[1])
    for sigma in sys.argv[2:]:
        t0 = time.time()
        print(sigma, shield_sat(sigma, nmax), "%.1fs" % (time.time() - t0), flush=True)
