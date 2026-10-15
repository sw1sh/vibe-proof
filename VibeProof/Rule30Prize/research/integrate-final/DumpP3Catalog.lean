import Ruliology.CellularAutomata.Rule30EtherThree
import Ruliology.CellularAutomata.Rule30EtherThreeNoWall
import Ruliology.CellularAutomata.Rule30EtherThreeTrap
import Ruliology.CellularAutomata.Rule30EtherThreeReach
import Ruliology.CellularAutomata.Rule30EtherThreeLeft
import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton
import Lean

/-! Fingerprint of every constant under `Ruliology.CellularAutomata.Rule30EtherThree` in the scratch
build of p3-ether (before integration): name, kind, universe parameters, hash of the type, hash of
the value (definitions) or `thm:` hash of the proof term (theorems). -/

open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def dumpConsts (pre : Name) (out : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  let lines := env.constants.fold (fun (acc : Array String) n ci =>
    if pre.isPrefixOf n then
      let v := match ci with
        | .defnInfo d => toString d.value.hash
        | .thmInfo t => "thm:" ++ toString t.value.hash
        | _ => "-"
      acc.push s!"{n} {kindOf ci} {ci.levelParams} {ci.type.hash} {v}"
    else acc) #[]
  let sorted := lines.qsort (· < ·)
  IO.FS.writeFile out (String.intercalate "\n" sorted.toList ++ "\n")
  IO.println s!"wrote {sorted.size} lines to {out}"

#eval dumpConsts `Ruliology.CellularAutomata.Rule30EtherThree
  "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/p3_catalog.txt"
