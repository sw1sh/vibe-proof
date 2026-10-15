import Lean
import Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
open Lean Elab Command

/-- All constants reachable from `n` through types and values (theorem proofs included). -/
partial def reach (env : Environment) (n : Name) (seen : NameSet) : NameSet := Id.run do
  if seen.contains n then return seen
  let mut s := seen.insert n
  match env.find? n with
  | none => return s
  | some ci =>
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do s := reach env c s
    return s

#eval show CommandElabM Unit from do
  let env ← getEnv
  let base := `Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
  let r := reach env (base ++ `q01_width_le_52) {}
  let mut missing : Array Nat := #[]
  for i in List.range 256 do
    let c := Name.mkStr (Name.mkStr base s!"C{i / 16}") s!"c{i}"
    if !r.contains c then missing := missing.push i
  -- each chunk theorem's type must be exactly `check 52 97 18 i = true`
  let mut badTy : Array Nat := #[]
  for i in List.range 256 do
    let c := Name.mkStr (Name.mkStr base s!"C{i / 16}") s!"c{i}"
    let some ci := env.find? c | badTy := badTy.push i; continue
    let want := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst `Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.check) #[mkNatLit 52, mkNatLit 97, mkNatLit 18, mkNatLit i])
      (mkConst ``Bool.true)
    if !(← liftTermElabM <| Meta.isDefEq ci.type want) || ci.type.getUsedConstants.toList.any (fun k => k != ``Eq && k != ``Bool && k != ``Bool.true && k != `Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.check && k != ``OfNat.ofNat && k != ``instOfNatNat && k != ``Nat) then
      badTy := badTy.push i
  logInfo m!"q01_width_le_52 reaches {r.size} constants; chunk theorems missing from its closure: {missing.size} {missing}; chunk theorems with unexpected type: {badTy.size} {badTy}"
