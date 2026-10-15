#!/usr/bin/env python3
"""Print docstring + statement of Lean declarations.

usage: stmts.py FILE [NAME ...]    (no names: list every theorem/lemma/def with line numbers)
A statement is everything from the `theorem NAME` line up to the first `:=` at depth 0
(or 40 lines at most).
"""
import re, sys

path = sys.argv[1]
names = sys.argv[2:]
src = open(path, encoding="utf-8").read().split("\n")
decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s:({\[]+)")

if not names:
    for i, line in enumerate(src):
        m = decl.match(line)
        if m:
            print(f"{i+1}: {m.group(1)} {m.group(2)}")
    sys.exit(0)

def doc_before(i):
    # collect a /-- ... -/ docstring ending right above line i
    j = i - 1
    while j >= 0 and src[j].strip() == "":
        j -= 1
    if j < 0 or not src[j].rstrip().endswith("-/"):
        return ""
    k = j
    while k >= 0 and "/--" not in src[k]:
        k -= 1
    if k < 0:
        return ""
    return "\n".join(src[k:j + 1])

for name in names:
    found = False
    for i, line in enumerate(src):
        m = decl.match(line)
        if m and (m.group(2) == name or m.group(2).endswith("." + name)):
            found = True
            d = doc_before(i)
            out = []
            for k in range(i, min(i + 40, len(src))):
                out.append(src[k])
                if ":=" in src[k] or src[k].rstrip().endswith(" where"):
                    break
            print(f"--- {name} (line {i+1})")
            if d:
                print(d)
            print("\n".join(out))
            break
    if not found:
        print(f"--- {name}: NOT FOUND")
