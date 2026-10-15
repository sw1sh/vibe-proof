import re, json, sys

README = "/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize/lean/README.md"
OUT = "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/snapshot/verify/"

txt = open(README, encoding="utf-8").read()
rows = []
for line in txt.splitlines():
    if not line.startswith("| `"):
        continue
    # split on unescaped pipes
    cells = [c.strip() for c in re.split(r"(?<!\\)\|", line)[1:-1]]
    if len(cells) != 4:
        continue
    mod_cell, added, what, heads = cells
    mods = re.findall(r"`([^`]+)`", mod_cell)
    names = re.findall(r"`([^`]+)`", heads)
    rows.append({"module": mods[0], "added": added, "what": what, "heads": names})

# README namespace rules
def ns_of(mod):
    if mod in ("Rule30Predecessors", "Rule30PredecessorCounts"):
        return "Rule30"
    if mod.startswith("Rule30EtherThree"):
        return "Rule30EtherThree"
    if mod == "Rule30EtherTrapWidth20":
        return "Rule30EtherTrap"
    if mod == "Rule30ZeroBoundaryStripeFamily":
        return "Rule30ZeroBoundaryStripeFront"
    return mod

pairs = []
for r in rows:
    m = r["module"]
    if "/" in m:
        continue  # data modules, no headline theorems
    for n in r["heads"]:
        full = f"Ruliology.CellularAutomata.{ns_of(m)}.{n}"
        pairs.append((f"Ruliology.CellularAutomata.{m}", n, full))

json.dump(rows, open(OUT + "readme_rows.json", "w"), indent=1)
print("rows:", len(rows), "pairs:", len(pairs))
mods_in_tables = [r["module"] for r in rows]
print("modules in tables:", len(mods_in_tables))
print("added labels:", sorted(set(r["added"] for r in rows)))

# Lean file 1: existence + module membership for each pair (meta), plus print the type
lines = ["import Ruliology", "import Lean", "open Lean", "",
         "def pairs : List (String × String × String) := ["]
lines.append(",\n".join(f'  ("{a}", "{b}", "{c}")' for a, b, c in pairs))
lines.append("]")
lines.append(r'''
def nameEndsWith (n : Name) (suffix : List String) : Bool :=
  let comps := n.components.map (fun c => c.toString)
  comps.length ≥ suffix.length && comps.drop (comps.length - suffix.length) == suffix

#eval show CoreM Unit from do
  let env ← getEnv
  let mnames := env.header.moduleNames
  for (modStr, nm, fullStr) in pairs do
    let full := fullStr.toName
    let modName := modStr.toName
    let declMod : String := match env.getModuleIdxFor? full with
      | some idx => toString (mnames[idx.toNat]!)
      | none => "NONE"
    let exists_ := (env.find? full).isSome
    let kind : String := match env.find? full with
      | some (.thmInfo _) => "thm"
      | some (.defnInfo _) => "def"
      | some (.axiomInfo _) => "AXIOM"
      | some (.opaqueInfo _) => "opaque"
      | some (.inductInfo _) => "inductive"
      | some (.ctorInfo _) => "ctor"
      | some _ => "other"
      | none => "-"
    if exists_ && declMod == modStr then
      IO.println s!"OK   {fullStr} [{kind}]"
    else
      -- search the module for any constant ending with the given suffix
      let hits : Array Name := match env.getModuleIdx? modName with
        | some idx => (env.header.moduleData[idx.toNat]!).constNames.filter (fun c => nameEndsWith c (nm.splitOn "."))
        | none => #[]
      IO.println s!"BAD  {fullStr} exists={exists_} declMod={declMod} expectedMod={modStr} hitsInModule={hits.toList}"
''')
open(OUT + "Names.lean", "w").write("\n".join(lines))

# Lean file 2: #print axioms for every headline constant
al = ["import Ruliology", ""]
for a, b, c in pairs:
    al.append(f"#print axioms {c}")
open(OUT + "AxiomsHeadline.lean", "w").write("\n".join(al) + "\n")
print("wrote Names.lean, AxiomsHeadline.lean")
