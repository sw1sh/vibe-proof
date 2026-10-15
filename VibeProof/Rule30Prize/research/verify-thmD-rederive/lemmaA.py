# Independent check of Lemma A and related local facts for rule 30.
# rule(l, c, r) = l xor (c or r)   (rule 30: 00011110)
import itertools

def rule(l, c, r):
    return l ^ (c | r)

# sanity: rule-30 truth table, Wolfram numbering: bit (4l+2c+r) of 30
for l, c, r in itertools.product((0, 1), repeat=3):
    assert rule(l, c, r) == (30 >> (4 * l + 2 * c + r)) & 1

def step_driven(left, row):
    """One step of the half-row to the right of a driver cell `left`.
    row[i] is column m+1+i. Output is one cell shorter (rightmost cell lacks its right neighbour)."""
    out = []
    for i in range(len(row) - 1):
        l = left if i == 0 else row[i - 1]
        out.append(rule(l, row[i], row[i + 1]))
    return out

# Lemma A: column m black at times t..t+8, any 11 cells m+1..m+11 at time t
# => at time t+9 columns m+1, m+2 are (0, 1).
bad = 0
for bits in itertools.product((0, 1), repeat=11):
    row = list(bits)
    for _ in range(9):
        row = step_driven(1, row)
    assert len(row) == 2
    if row != [0, 1]:
        bad += 1
print("Lemma A failures over 2^11 rows:", bad)

# Is 9 the least such number?  (informational)
for n in range(1, 10):
    w = n + 2
    outs = set()
    for bits in itertools.product((0, 1), repeat=w):
        row = list(bits)
        for _ in range(n):
            row = step_driven(1, row)
        outs.add(tuple(row))
    print(f"n={n} black steps: possible (col m+1, col m+2) after = {sorted(outs)}")

# Brute-force Lemma A* for j = 1, 2 directly (9j steps, 2j cells), as a cross-check of the induction.
for j in (1,):
    n = 9 * j
    w = n + 2 * j
    outs = set()
    for bits in itertools.product((0, 1), repeat=w):
        row = list(bits)
        for _ in range(n):
            row = step_driven(1, row)
        outs.add(tuple(row))
    print(f"Lemma A* j={j}: outcomes {outs}")

# Step facts used in Theorem D:
assert rule(0, 0, 1) == 1          # cell(e_k+1, 1) = rule(c=0, 0, 1) = 1
assert all(rule(0, 1, x) == 1 for x in (0, 1))   # column 1 stays black while column 0 is white
print("rule(0,0,1) =", rule(0, 0, 1), "; rule(0,1,x) =", [rule(0, 1, x) for x in (0, 1)])
