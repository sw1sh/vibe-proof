# Canonical pre-history of rule 30: rows -1,-2,... obtained from row 0 (single cell) by the unique
# right-edge-anchored inverse  y_i(t-1) = y_i(t) xor (y_{i-1}(t-1) or y_{i-2}(t-1)),  y_0 = 1.
# Print rows -1..-K as strings, index i = distance from the right edge (leftwards).
import sys
I = int(sys.argv[1]); K = int(sys.argv[2])
y = [1] + [0]*I
rows = []
for k in range(1, K+1):
    z = [0]*(I+1); z[0] = 1
    for i in range(1, I+1):
        a = z[i-1]; b = z[i-2] if i >= 2 else 0
        z[i] = y[i] ^ (a | b)
    y = z
    rows.append(z)
for k, r in enumerate(rows, 1):
    s = ''.join('#' if v else '.' for v in r)
    print(f"{-k:5d} {s}")
