import Lean
import Ruliology
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if (`Ruliology).isPrefixOf n then out := out.push n.toString
  for m in env.header.moduleNames do
    out := out.push s!"MODULE {m}"
  IO.FS.writeFile "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/verify/all_names.txt" (String.intercalate "\n" out.toList)
  logInfo m!"dumped {out.size}"
