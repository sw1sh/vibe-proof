import sys, random
sys.path.insert(0, '.')
from rightZ2 import run_right, ev_period
random.seed(int(sys.argv[1])); Tlo, Thi, steps = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
for w in sys.argv[5:]:
    P = len(w); full = 0; n = 0; Ts = []
    for trial in range(6):
        T = random.randint(Tlo, Thi)
        state = random.getrandbits(T - 1) | (1 << (T - 1))
        col = run_right(state, T, w, steps)
        ep = ev_period(col, lambda k: True, P, maxmult=16)
        n += 1
        if ep: full += 1; Ts.append(ep[0])
    print(w, f"T in [{Tlo},{Thi}] steps {steps}: absorbed {full}/{n}, transients {Ts}")
