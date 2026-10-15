import sys
w = sys.argv[1]; x = int(sys.argv[2], 16); ph = int(sys.argv[3]); L = int(sys.argv[4]); steps = int(sys.argv[5])
P = len(w); cw = [int(ch) for ch in w]
row = x; W = L + steps + 2
for t in range(steps):
    c = cw[(ph+t) % P]; cn = cw[(ph+t+1) % P]
    s = ''.join('#' if (row >> i) & 1 else '.' for i in range(W-1, -1, -1))
    flag = ''
    if c == 1 and (row & 1) != 1 - cn: flag = '  <-- violation'
    print(f"{t:3d} {s}|{'#' if c else '.'}{flag}")
    if flag: break
    right = ((row << 1) | c); left = row >> 1
    row = (left ^ (row | right)) & ((1 << W) - 1)
