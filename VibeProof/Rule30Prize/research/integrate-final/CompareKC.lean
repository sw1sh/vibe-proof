import KC.Q01W52
import KC.StripeFamily
import KC.EtherTrapMain
import KC.PeriodTwoW5
import KC.PeriodTwoW6
import Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily
import Ruliology.CellularAutomata.Rule30EtherTrapWidth20
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth5
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth6
import Lean

/-! Compare the scratch `KC.*` constants (kernel-certify-r2 t1–t4) with the catalog constants,
modulo the namespace renaming: same set of names, same kinds and universe parameters, identical
types, identical definition bodies, and (reported separately) identical proof terms. -/

open Lean

def renames : List (Name × Name) := [
  (`Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes, `KC.Q01Lanes),
  (`Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52, `KC.Q01W52),
  (`Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront, `KC.StripeFront),
  (`Ruliology.CellularAutomata.Rule30EtherTrap, `KC.EtherTrap),
  (`Ruliology.CellularAutomata.Rule30PeriodTwoLanguage, `KC.PeriodTwoLang),
  (`Ruliology.CellularAutomata.Rule30PeriodTwoWidth5, `KC.PeriodTwoW5),
  (`Ruliology.CellularAutomata.Rule30PeriodTwoWidth6, `KC.PeriodTwoW6)]

def catPrefix? (n : Name) : Option (Name × Name) := renames.find? (fun p => p.1.isPrefixOf n)
def kcPrefix? (n : Name) : Option (Name × Name) := renames.find? (fun p => p.2.isPrefixOf n)

def ren (n : Name) : Name :=
  match catPrefix? n with
  | some (a, b) => n.replacePrefix a b
  | none => n

def renExpr (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const (ren n) us)
    | _ => none

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def compareKC (out : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  let all := env.constants.fold (fun (acc : Array (Name × ConstantInfo)) n ci => acc.push (n, ci)) #[]
  let mut nCat := 0
  let mut nKC := 0
  let mut nTypeOK := 0
  let mut nDefOK := 0
  let mut nDefs := 0
  let mut nThms := 0
  let mut nThmSame := 0
  let mut problems : Array String := #[]
  let mut thmDiff : Array String := #[]
  for (n, ci) in all do
    if (kcPrefix? n).isSome then nKC := nKC + 1
    if (catPrefix? n).isSome then
      nCat := nCat + 1
      let k := ren n
      match env.find? k with
      | none => problems := problems.push s!"MISSING in scratch: {n} -> {k}"
      | some kci =>
        if kindOf ci != kindOf kci then problems := problems.push s!"KIND {n}: {kindOf ci} vs {kindOf kci}"
        if ci.levelParams != kci.levelParams then problems := problems.push s!"LEVELS {n}"
        if renExpr ci.type == kci.type then nTypeOK := nTypeOK + 1
        else problems := problems.push s!"TYPE differs: {n}"
        match ci, kci with
        | .defnInfo d, .defnInfo kd =>
          nDefs := nDefs + 1
          if renExpr d.value == kd.value then nDefOK := nDefOK + 1
          else problems := problems.push s!"DEF VALUE differs: {n}"
        | .thmInfo t, .thmInfo kt =>
          nThms := nThms + 1
          if renExpr t.value == kt.value then nThmSame := nThmSame + 1
          else thmDiff := thmDiff.push s!"{n}"
        | _, _ => pure ()
  -- every scratch constant has a catalog counterpart
  for (n, _) in all do
    match kcPrefix? n with
    | some (a, b) =>
      let c := n.replacePrefix b a
      if !(env.contains c) then problems := problems.push s!"MISSING in catalog: {n} -> {c}"
    | none => pure ()
  let summary := s!"catalog constants: {nCat}; scratch constants: {nKC}; types identical: {nTypeOK}; " ++
    s!"defs identical: {nDefOK}/{nDefs}; theorem proof terms identical: {nThmSame}/{nThms}; " ++
    s!"problems: {problems.size}"
  IO.FS.writeFile out (summary ++ "\n" ++ String.intercalate "\n" problems.toList ++
    "\n-- theorems whose proof terms differ (types identical):\n" ++
    String.intercalate "\n" (thmDiff.qsort (· < ·)).toList ++ "\n")
  IO.println summary
  for p in problems[:20] do IO.println p
  IO.println s!"theorems with different proof terms: {thmDiff.size}"
  for p in (thmDiff.qsort (· < ·))[:20] do IO.println s!"  {p}"

#eval compareKC "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/compare_kc.txt"
