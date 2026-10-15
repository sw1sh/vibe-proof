# Verify: spatially 7-periodic configuration ...1000000 1000000... is temporally 4-periodic under rule 30 and
# column 1 alternates.  Then truncations to [-n, n] (finite configs) keep column 1 alternating for ~n steps.
def r30_ring(x):
    q = len(x)
    return [x[(i - 1) % q] ^ (x[i] | x[(i + 1) % q]) for i in range(q)]
x = [1, 0, 0, 0, 0, 0, 0]
rows = [x]
for t in range(8):
    rows.append(r30_ring(rows[-1]))
for t, r in enumerate(rows): print(t, ''.join(map(str, r)))
print('period 4:', rows[4] == rows[0], ' column 1 series:', [r[1] for r in rows])
# finite truncations on the line: cells p in [-n, n] taken from the periodic pattern (cell p = x[p mod 7]), zero outside
def evolve_line(cells, lo, T):
    # cells: dict p->bit over [lo, lo+len); returns list of rows as dicts via arrays with margin
    W = len(cells); off = T + 2
    row = [0] * off + cells + [0] * off
    out = [row]
    for t in range(T):
        row = [0] + [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)] + [0]
        out.append(row)
    return out, off - lo
for n in (14, 28, 56, 112):
    lo = -n; cells = [x[p % 7] for p in range(-n, n + 1)]
    T = 3 * n
    rows_l, shift = evolve_line(cells, lo, T)
    col = [r[1 + shift] for r in rows_l]
    # first time column 1 fails to alternate (relative to its value at t = 0)
    fail = next((t for t in range(T + 1) if col[t] != (col[0] + t) % 2), None)
    print(f'truncation to [-{n},{n}]: column 1 alternates until t = {fail}')
