def right_run(state, width, cf, steps):
    row = state; W = width; col = []
    for t in range(steps):
        col.append(row & 1)
        W += 1; mask = (1 << W) - 1
        leftn = ((row << 1) | cf(t)) & mask
        row = (leftn ^ (row | (row >> 1))) & mask
    return col

def left_run(state, width, cf, steps):
    # bit k <-> position p = -k-1
    row = state; W = width; col = []
    for t in range(steps):
        col.append(row & 1)
        W += 1; mask = (1 << W) - 1
        rightn = ((row << 1) | cf(t)) & mask   # value at p+1 (bit 0 gets c(t))
        leftn = row >> 1                        # value at p-1
        row = (leftn ^ (row | rightn)) & mask
    return col

