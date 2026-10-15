import importlib.util, sys
spec = importlib.util.spec_from_file_location("sim", sys.argv[1])
# re-implement run() locally to avoid executing the sweep in sim_a1.py
def run(n, T):
    size = n + T + 5
    row = [0] * (size + 2)
    for k in range(1, n + 1, 2):
        row[k] = 1
    hist = [row[1]]
    for t in range(T):
        new = [0] * (size + 2)
        for k in range(1, size + 1):
            new[k] = row[k + 1] ^ (row[k] | row[k - 1])
        row = new
        hist.append(row[1])
    return hist
res = {}
for n in range(1, 202, 2):
    h = run(n, 3 * n + 20)
    od = next((t for t in range(1, len(h), 2) if h[t] == 0), None)
    res[n] = od
print("odd-phase first white odd time minus n, odd n<=201:", {n: (res[n] - n if res[n] is not None else None) for n in res if res[n] is None or res[n] - n > 8})
print("n=81 odd-phase death:", res[81])
