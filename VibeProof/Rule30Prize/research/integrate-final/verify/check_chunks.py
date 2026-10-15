"""Independent check of the W52 chunk regrouping (scratch KC.Q01W52.C0..C15 -> catalog Chunks0..3).

Checks:
  * every chunk theorem c{i}, i < 256, appears exactly once in the catalog, in namespace C{i // 16},
    with statement `check 52 97 18 i = true` proved by `decide +kernel`;
  * the catalog theorem lines are byte-identical to the scratch lines (same namespace, same text);
  * each `range` theorem in C{j} has type `ChunksOK 52 97 18 (16 j) 16` and a proof term that uses
    chunksOK_one c{16j}..c{16j+15}, each exactly once and in order, and is byte-identical to scratch;
  * the main Width52 module's `all_chunks` uses C0.range..C15.range, each exactly once and in order;
  * nothing else (no extra declarations) is in the chunk modules.
"""
import re
import sys

SCR = "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t1/src/KC"
CAT = "/Users/swish/src/wolfram/vibe-proof/ruliology-lean/Ruliology/CellularAutomata"

errors = []


def decls(path):
    """Return list of (namespace, declaration text) for every top-level declaration in the file.
    A declaration starts at a line beginning with theorem/def/lemma/abbrev/instance/... and runs
    until the next blank line or `end`/`namespace` line."""
    ns_stack = []
    out = []
    cur = None
    in_comment = 0
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    for line in lines:
        s = line.strip()
        # track block comments /- ... -/ (docstrings); declarations never start inside them
        if in_comment:
            in_comment += s.count("/-") - s.count("-/")
            continue
        if s.startswith("/-"):
            in_comment = s.count("/-") - s.count("-/")
            if cur is not None:
                out.append(cur)
                cur = None
            continue
        m = re.match(r"^namespace\s+(\S+)$", s)
        if m:
            if cur is not None:
                out.append(cur); cur = None
            ns_stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+(\S+)$", s)
        if m:
            if cur is not None:
                out.append(cur); cur = None
            if not ns_stack or ns_stack[-1] != m.group(1):
                errors.append(f"{path}: unbalanced end {m.group(1)} (stack {ns_stack})")
            else:
                ns_stack.pop()
            continue
        if re.match(r"^(theorem|lemma|def|abbrev|instance|axiom|opaque|noncomputable|private|protected|@\[|example|structure|inductive|class)\b", s):
            if cur is not None:
                out.append(cur)
            cur = (".".join(ns_stack), line)
            continue
        if s == "" or s.startswith("import") or s.startswith("open"):
            if cur is not None:
                out.append(cur); cur = None
            continue
        if cur is not None:
            cur = (cur[0], cur[1] + "\n" + line)
        else:
            errors.append(f"{path}: stray line outside declaration: {line[:120]!r}")
    if cur is not None:
        out.append(cur)
    if ns_stack:
        errors.append(f"{path}: unclosed namespaces {ns_stack}")
    return out


# scratch: 16 files, namespace KC.Q01W52.C{j}
scratch = {}
for j in range(16):
    for ns, text in decls(f"{SCR}/Q01W52/C{j}.lean"):
        if ns != f"KC.Q01W52.C{j}":
            errors.append(f"scratch C{j}: unexpected namespace {ns}")
        name = re.match(r"^theorem\s+(\S+)", text).group(1)
        key = (j, name)
        if key in scratch:
            errors.append(f"scratch duplicate {key}")
        scratch[key] = text

# catalog: 4 files, namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.C{j}
catalog = {}
for k in range(4):
    for ns, text in decls(f"{CAT}/Rule30Certificates/ZeroBoundaryWidth52Chunks{k}.lean"):
        m = re.match(r"^Ruliology\.CellularAutomata\.Rule30ZeroBoundaryWidth52\.C(\d+)$", ns)
        if not m:
            errors.append(f"catalog Chunks{k}: declaration outside C-namespace: ns={ns!r} {text[:80]!r}")
            continue
        j = int(m.group(1))
        if not (4 * k <= j < 4 * k + 4):
            errors.append(f"catalog Chunks{k}: namespace C{j} not in its block")
        name = re.match(r"^theorem\s+(\S+)", text).group(1)
        key = (j, name)
        if key in catalog:
            errors.append(f"catalog duplicate {key}")
        catalog[key] = text

if set(scratch) != set(catalog):
    errors.append(f"key sets differ: only scratch {sorted(set(scratch) - set(catalog))[:10]}, "
                  f"only catalog {sorted(set(catalog) - set(scratch))[:10]}")

for key in sorted(set(scratch) & set(catalog)):
    if scratch[key] != catalog[key]:
        errors.append(f"text differs for {key}")

# chunk theorems
seen = []
for (j, name), text in catalog.items():
    m = re.match(r"^c(\d+)$", name)
    if m:
        i = int(m.group(1))
        seen.append(i)
        if i // 16 != j:
            errors.append(f"c{i} in namespace C{j}")
        want = f"theorem c{i} : check 52 97 18 {i} = true := by decide +kernel"
        if text != want:
            errors.append(f"c{i}: unexpected text {text!r}")
    elif name == "range":
        m2 = re.match(r"^theorem range : ChunksOK 52 97 18 (\d+) 16 :=\n  (.*)$", text, re.S)
        if not m2:
            errors.append(f"C{j}.range: unexpected header {text[:100]!r}")
            continue
        if int(m2.group(1)) != 16 * j:
            errors.append(f"C{j}.range: lo = {m2.group(1)}, expected {16 * j}")
        used = [int(x) for x in re.findall(r"chunksOK_one c(\d+)\)", m2.group(2))]
        if used != list(range(16 * j, 16 * j + 16)):
            errors.append(f"C{j}.range uses {used}")
        rest = re.sub(r"chunksOK_append|chunksOK_one c\d+|[()\s]", "", m2.group(2))
        if rest:
            errors.append(f"C{j}.range: unexpected tokens {rest!r}")
    else:
        errors.append(f"unexpected declaration C{j}.{name}")

if sorted(seen) != list(range(256)):
    errors.append(f"chunk indices: {len(seen)} found, missing {sorted(set(range(256)) - set(seen))[:10]}, "
                  f"dups {[i for i in set(seen) if seen.count(i) > 1][:10]}")

# main theorem consumes all ranges
with open(f"{CAT}/Rule30ZeroBoundaryWidth52.lean", encoding="utf-8") as f:
    main = f.read()
m = re.search(r"theorem all_chunks : ChunksOK 52 97 18 0 256 :=\n  (.*?)\n\n", main, re.S)
if not m:
    errors.append("all_chunks not found with expected type")
else:
    used = [int(x) for x in re.findall(r"C(\d+)\.range", m.group(1))]
    if used != list(range(16)):
        errors.append(f"all_chunks uses ranges {used}")
    rest = re.sub(r"chunksOK_append|C\d+\.range|[()\s]", "", m.group(1))
    if rest:
        errors.append(f"all_chunks: unexpected tokens {rest!r}")

print(f"scratch decls: {len(scratch)}, catalog decls: {len(catalog)}, chunk theorems: {len(seen)}")
print("ERRORS:" if errors else "OK: no errors")
for e in errors:
    print("  ", e)
sys.exit(1 if errors else 0)
