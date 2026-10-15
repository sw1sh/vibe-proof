import Ruliology
import Lean
open Lean

/-- Independent axiom sweep: walks constant bodies directly (types, values, constructors,
recursor rules) instead of reading the per-module axiom tables stored in the oleans. -/
def sweep (env : Environment) (roots : Array Name) : NameSet × Nat × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut axs : NameSet := {}
  let mut missing : Array Name := #[]
  let mut stack : Array Name := roots
  let mut count := 0
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    count := count + 1
    let mut deps : Array Name := #[]
    match env.find? c with
    | some (.axiomInfo v) =>
        axs := axs.insert c
        deps := v.type.getUsedConstants
    | some (.defnInfo v) => deps := v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => deps := v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => deps := v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.quotInfo v) => deps := v.type.getUsedConstants
    | some (.ctorInfo v) => deps := v.type.getUsedConstants.push v.induct
    | some (.recInfo v) =>
        deps := v.type.getUsedConstants ++ v.all.toArray
        for r in v.rules do
          deps := deps ++ r.rhs.getUsedConstants
    | some (.inductInfo v) => deps := v.type.getUsedConstants ++ v.ctors.toArray ++ v.all.toArray
    | none => missing := missing.push c
    for d in deps do
      if !seen.contains d then stack := stack.push d
  return (axs, count, missing)

#eval show CoreM Unit from do
  let env ← getEnv
  let mnames := env.header.moduleNames
  let mut roots : Array Name := #[]
  let mut nMods := 0
  let mut declaredAxioms : Array Name := #[]
  let mut unsafeDefs : Array Name := #[]
  let mut partialDefs : Array Name := #[]
  let mut opaques : Array Name := #[]
  for h : i in [0:mnames.size] do
    let m := mnames[i]
    if (`Ruliology).isPrefixOf m then
      nMods := nMods + 1
      let data := env.header.moduleData[i]!
      for ci in data.constants do
        roots := roots.push ci.name
        match ci with
        | .axiomInfo _ => declaredAxioms := declaredAxioms.push ci.name
        | .defnInfo v =>
            if v.safety == .unsafe then unsafeDefs := unsafeDefs.push ci.name
            if v.safety == .partial then partialDefs := partialDefs.push ci.name
        | .opaqueInfo _ => opaques := opaques.push ci.name
        | _ => pure ()
  IO.println s!"Ruliology modules: {nMods}"
  IO.println s!"Ruliology constants (moduleData.constants): {roots.size}"
  IO.println s!"declared axioms in Ruliology: {declaredAxioms.toList}"
  IO.println s!"unsafe defs: {unsafeDefs.size} {unsafeDefs.toList.take 10}"
  IO.println s!"partial defs: {partialDefs.size} {partialDefs.toList.take 10}"
  IO.println s!"opaque consts: {opaques.size} {opaques.toList.take 10}"
  let (axs, cnt, missing) := sweep env roots
  IO.println s!"constants visited (transitive): {cnt}; unresolved: {missing.size} {missing.toList.take 10}"
  IO.println s!"axioms reachable (independent walk): {axs.toList}"
  -- cross-check with Lean.collectAxioms (uses the olean axiom tables)
  let mut union : NameSet := {}
  let mut viol : Array Name := #[]
  for r in roots do
    let a ← collectAxioms r
    for x in a do
      union := union.insert x
      if !(x == ``propext || x == ``Classical.choice || x == ``Quot.sound) then
        viol := viol.push r
  IO.println s!"collectAxioms union over {roots.size} constants: {union.toList}; violating constants: {viol.size}"
