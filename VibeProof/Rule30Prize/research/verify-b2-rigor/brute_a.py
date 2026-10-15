# Independent brute-force check of step (a) and of the skeleton claims for the driven right half.
import itertools

def xor(a, b): return a ^ b

# c at phases 0..3 = 0,0,1,1
cph = [0, 0, 1, 1]

# (a): start at time s+1 (phase 1 of block k-1), columns 1..5 free, simulate 4 steps.
# Check: col1(s+5) == 0  ==>  col1(s+1) == 0, and also col1(s+2)==0, col1(s+3)==1, col1(s+4)==0
bad = 0
cnt0 = 0
for cfg in itertools.product([0, 1], repeat=5):
    row = [None] + list(cfg)  # row[1..5]
    hist = {1: row[:]}
    # times s+1 .. s+5 ; phase of time s+j is j%4 -> c value cph[j%4]
    cur = row
    rows = [cur]
    for j in range(1, 5):  # step from s+j to s+j+1 uses c(s+j)
        c = cph[j % 4]
        full = [c] + cur[1:]  # index 0 = column 0
        nxt = [None]
        for p in range(1, len(full) - 1):
            nxt.append(xor(full[p - 1], full[p] | full[p + 1]))
        cur = nxt
        rows.append(cur)
    # rows[i] holds columns 1..(5-i) at time s+1+i
    E1 = rows[4][1]
    if E1 == 0:
        cnt0 += 1
        A1, B1, C1, D1 = rows[0][1], rows[1][1], rows[2][1], rows[3][1]
        if not (A1 == 0 and B1 == 0 and C1 == 1 and D1 == 0):
            bad += 1
            print("counterexample", cfg)
print("step (a): configurations with col1(s+5)=0:", cnt0, "of 32; violations:", bad)

# (c) forward: col1(s+1)=1 => col1(s+2)=1 and col1(s+3)=0 regardless of others
bad = 0
for cfg in itertools.product([0, 1], repeat=3):
    a1, a2, b2 = cfg
    if a1 != 1: continue
    b1 = xor(cph[1], a1 | a2)
    c1 = xor(cph[2], b1 | b2)
    if not (b1 == 1 and c1 == 0): bad += 1
print("step (c) violations:", bad)

# column -1 via cell_left: cell t (-1) = c(t+1) xor (c(t) or cell t 1)
for ph in range(4):
    for x1 in (0, 1):
        m1 = xor(cph[(ph + 1) % 4], cph[ph] | x1)
        print("phase", ph, "col1", x1, "-> col-1", m1)
