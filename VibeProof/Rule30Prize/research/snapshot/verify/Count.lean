import Ruliology
import Lean
open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.allImportedModuleNames
  let viaFold := env.constants.fold (fun (acc : NameSet) n _ =>
    match env.getModuleIdxFor? n with
    | some idx => if (`Ruliology).isPrefixOf (mods[idx.toNat]!) then acc.insert n else acc
    | none => acc) {}
  let mut viaData : NameSet := {}
  let mut viaNames : NameSet := {}
  let mut nData := 0
  for h : i in [0:mods.size] do
    if (`Ruliology).isPrefixOf mods[i] then
      let d := env.header.moduleData[i]!
      nData := nData + d.constants.size
      for c in d.constants do viaData := viaData.insert c.name
      for c in d.constNames do viaNames := viaNames.insert c
  IO.println s!"fold: {viaFold.size}  moduleData.constants: {nData} (distinct {viaData.size})  constNames distinct: {viaNames.size}"
  for n in viaData do
    if !viaFold.contains n then
      IO.println s!"in moduleData but not fold: {n}; find? = {(env.find? n).isSome}; modIdx = {(env.getModuleIdxFor? n).map (fun i => mods[i.toNat]!)}"
  for n in viaFold do
    if !viaData.contains n then IO.println s!"in fold but not moduleData: {n}"
