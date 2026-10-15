"""Classify every changed line between each scratch source and its catalog file.

A changed line is "allowed" if it is blank, an import/namespace/open/end line, or lies inside a
module docstring (/-! ... -/). Anything else (a changed code line or a changed declaration
docstring /-- ... -/) is reported. The W52 chunk files are handled by check_chunks.py.
"""
import difflib
import re
import sys

S = "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize"
C = "/Users/swish/src/wolfram/vibe-proof/ruliology-lean/Ruliology/CellularAutomata"
PAIRS = [l.split() for l in open(f"{S}/integrate-final/verify/pairs.txt") if l.strip()]


def classify(lines):
    """For each line, return its kind: 'moddoc', 'decldoc', 'comment', or 'code'."""
    kinds = []
    mode = None  # None, 'moddoc', 'decldoc', 'comment'
    depth = 0
    for line in lines:
        s = line.strip()
        if mode is None:
            if s.startswith("/-!"):
                mode = "moddoc"
            elif s.startswith("/--"):
                mode = "decldoc"
            elif s.startswith("/-"):
                mode = "comment"
            if mode is not None:
                depth = line.count("/-") - line.count("-/")
                kinds.append(mode)
                if depth <= 0:
                    mode = None
                continue
            kinds.append("code")
        else:
            kinds.append(mode)
            depth += line.count("/-") - line.count("-/")
            if depth <= 0:
                mode = None
    return kinds


STRUCT = re.compile(r"^\s*(import\s|namespace\s|open\s|end\s|$)")
bad_total = 0
for cat, scr in PAIRS:
    a = open(f"{S}/{scr}", encoding="utf-8").read().split("\n")
    b = open(f"{C}/{cat}.lean", encoding="utf-8").read().split("\n")
    ka, kb = classify(a), classify(b)
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    bad = []
    counts = {}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        for side, lines, kinds, rng in (("-", a, ka, range(i1, i2)), ("+", b, kb, range(j1, j2))):
            for i in rng:
                k = kinds[i]
                if k == "code" and STRUCT.match(lines[i]):
                    k = "struct"
                counts[k] = counts.get(k, 0) + 1
                if k not in ("moddoc", "struct"):
                    bad.append(f"{side}{i + 1} [{k}] {lines[i][:150]}")
    print(f"{cat}: changed-line kinds {counts}")
    for x in bad:
        print("    UNEXPECTED", x)
    bad_total += len(bad)
print("TOTAL unexpected changed lines:", bad_total)
sys.exit(1 if bad_total else 0)
