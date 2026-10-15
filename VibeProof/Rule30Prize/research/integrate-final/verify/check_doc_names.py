"""Resolve every backticked identifier-like token in the module docstrings (/-! ... -/) of the
28 new files against the catalog's constants, namespaces and modules. Prints unresolved tokens."""
import re

V = "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/verify"
ROOT = "/Users/swish/src/wolfram/vibe-proof/ruliology-lean"
CA = "Ruliology.CellularAutomata"

consts, modules = set(), set()
for line in open(f"{V}/all_names.txt", encoding="utf-8"):
    line = line.strip()
    if line.startswith("MODULE "):
        modules.add(line[7:])
    elif line:
        consts.add(line)
namespaces = set()
for c in consts:
    parts = c.split(".")
    for i in range(1, len(parts)):
        namespaces.add(".".join(parts[:i]))

IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.₀-₉]*$")
unresolved = []
total = 0
for rel in open(f"{V}/new_list.txt"):
    rel = rel.strip()
    if not rel:
        continue
    text = open(f"{ROOT}/{rel}", encoding="utf-8").read()
    # file namespaces and opens, for resolution context
    nss = re.findall(r"^namespace\s+(\S+)", text, re.M)
    full_ns = []
    acc = ""
    for n in nss:
        full = n if n.startswith("Ruliology") else (acc + "." + n if acc else n)
        full_ns.append(full)
        acc = full
    opens = []
    for o in re.findall(r"^open\s+(.+)$", text, re.M):
        opens += o.split()
    prefixes = set(full_ns) | {CA, ""} | {f"{CA}.{o}" for o in opens}
    for doc in re.findall(r"/-!(.*?)-/", text, re.S):
        for tok in re.findall(r"`([^`]+)`", doc):
            if not IDENT.match(tok) or tok.isdigit():
                continue
            total += 1
            cands = [f"{p}.{tok}" if p else tok for p in prefixes]
            ok = any(c in consts or c in namespaces or c in modules for c in cands)
            if not ok:
                unresolved.append((rel.split("/")[-1], tok))
print(f"identifier-like tokens: {total}; unresolved: {len(unresolved)}")
for f, t in unresolved:
    print(f"  {f}: `{t}`")
