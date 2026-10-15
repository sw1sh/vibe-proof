import Ruliology
import Lean
open Lean Ruliology.CellularAutomata

#eval Rule30Ether.wallStates.length
#eval Rule30StripCertificateTable.certTable.length
#eval (Rule30StripCertificateTable.certTable.map (fun e => e.1)).mergeSort
#eval ((Rule30StripCertificateTable.certTable.map
        (fun e => Rule30StripCertificateTable.wordOf e.1 e.2.1)).eraseDups).length
#eval (Rule30EtherThree.t001.b, Rule30EtherThree.t001.m, Rule30EtherThree.t001.n)

/-- Is any constant of the snapshot a proof of exactly `target` (or of `¬ target`)? -/
def findProofs (target : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  let mnames := env.header.moduleNames
  let neg := mkApp (mkConst ``Not) target
  let mut hits := #[]
  for h : i in [0:mnames.size] do
    if (`Ruliology).isPrefixOf mnames[i] then
      for ci in (env.header.moduleData[i]!).constants do
        if ci.type == target || ci.type == neg then hits := hits.push ci.name
  return hits

#eval show CoreM Unit from do
  let R := `Ruliology.CellularAutomata
  let c (n : Name) : Expr := mkConst (R ++ n)
  let targets : List (String × Expr) := [
    ("Problem1", c `Rule30Prize.Problem1),
    ("Problem2", c `Rule30Prize.Problem2),
    ("PeriodTwo.Q01", c `Rule30PeriodTwo.Q01),
    ("ZeroBoundary.Q01", c `Rule30ZeroBoundary.Q01),
    ("CQ01", c `Rule30PeriodTwoCoupled.CQ01),
    ("Absorption w0001 A0001", mkApp2 (c `Rule30Ether.Absorption) (c `Rule30Ether.w0001) (c `Rule30Ether.A0001)),
    ("Absorption w0011 A0011", mkApp2 (c `Rule30Ether.Absorption) (c `Rule30Ether.w0011) (c `Rule30Ether.A0011)),
    ("Absorption w0111 A0111", mkApp2 (c `Rule30Ether.Absorption) (c `Rule30Ether.w0111) (c `Rule30Ether.A0111)),
    ("C3 w0001", mkApp (c `Rule30PeriodFourSkeleton.C3) (c `Rule30Ether.w0001)),
    ("C3 w0011", mkApp (c `Rule30PeriodFourSkeleton.C3) (c `Rule30Ether.w0011)),
    ("C3 w0111", mkApp (c `Rule30PeriodFourSkeleton.C3) (c `Rule30Ether.w0111)),
    ("AbsorptionT t001", mkApp (c `Rule30EtherThree.AbsorptionT) (c `Rule30EtherThree.t001)),
    ("Q001", c `Rule30EtherThree.Q001),
    ("C3w w011", mkApp (c `Rule30EtherThree.C3w) (c `Rule30EtherThree.w011)),
    ("C3s001", c `Rule30EtherThree.C3s001)]
  let env ← getEnv
  for (s, e) in targets do
    -- make sure the target constants exist
    let ok := e.getUsedConstants.all fun n => (env.find? n).isSome
    let hits ← findProofs e
    IO.println s!"{s}: constantsExist={ok} provedOrRefuted={hits.toList}"
