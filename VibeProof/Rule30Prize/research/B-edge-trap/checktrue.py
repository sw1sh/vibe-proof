# independent check: full rule 30 from a single cell vs. right half driven by the center column from the data file
T = 3000
c = []
data = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb').read(T // 8 + 2)
c = [(data[i >> 3] >> (7 - (i & 7))) & 1 for i in range(T + 1)]
# full pattern: positions -T-1..T+1 as int with offset
off = T + 2
row = 1 << off
for t in range(T):
    row = ((row << 1) ^ (row | (row >> 1))) & ((1 << (2 * off + 2)) - 1)
full_right = (row >> off)  # bit p = cell(T, p) for p >= 0
# driven right half
r = c[0]
for t in range(T):
    Wd = r.bit_length() + 2
    r = ((((r << 1) ^ (r | (r >> 1))) & ((1 << Wd) - 1)) & ~1) | c[t + 1]
print('center matches data:', (full_right & 1) == c[T], ' right halves equal:', full_right == r)
