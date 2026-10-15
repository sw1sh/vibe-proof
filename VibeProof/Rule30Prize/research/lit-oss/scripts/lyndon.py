def lyndon_words(n):
    w = [-1]
    while w:
        w[-1] += 1
        m = len(w)
        if m == n:
            yield tuple(w)
        while len(w) < n:
            w.append(w[len(w) - m])
        while w and w[-1] == 1:
            w.pop()
if __name__ == '__main__':
    import sys
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        for w in lyndon_words(n):
            s = ''.join(map(str, w))
            if n == 1: continue
            print(s)
