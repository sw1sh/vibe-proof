import sys
W = int(sys.argv[1]); ph = int(sys.argv[2]); X = int(sys.argv[3], 16); steps = int(sys.argv[4])
# left half cells: index i <-> position -(i+1); print positions -(W+steps)..-1 then | c
N = W + steps + 2
x = [(X >> i) & 1 if i < W else 0 for i in range(N)]
for t in range(steps):
    ct = (t + ph) % 2; cn = (t + 1 + ph) % 2
    viol = (ct == 1 and x[0] != 1 - cn)
    print('%4d' % t, ''.join('#' if x[i] else '.' for i in range(min(N, 70) - 1, -1, -1)), '|', ct, ' VIOLATION' if viol else '')
    if viol: break
    y = [x[i+1] ^ (x[i] | (ct if i == 0 else x[i-1])) if i + 1 < N else 0 for i in range(N)]
    x = y
