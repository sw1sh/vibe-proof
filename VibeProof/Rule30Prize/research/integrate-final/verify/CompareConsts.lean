import Lean
import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
import Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily
import Ruliology.CellularAutomata.Rule30EtherTrap
import Ruliology.CellularAutomata.Rule30EtherTrapWidth20
import Ruliology.CellularAutomata.Rule30PeriodTwoLanguage
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth5
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth6
import Ruliology.CellularAutomata.Rule30EtherThree
import Ruliology.CellularAutomata.Rule30EtherThreeNoWall
import Ruliology.CellularAutomata.Rule30EtherThreeTrap
import Ruliology.CellularAutomata.Rule30EtherThreeReach
import Ruliology.CellularAutomata.Rule30EtherThreeLeft
import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton

/-!
Independent Lean-level comparison of the scratch modules (rebuilt from source into
verify/scratchbuild) with the catalog modules. Scratch constants are read straight from the
scratch .olean files with `readModuleData` (never imported), renamed, and compared with the
catalog environment.
-/

open Lean Elab Command

namespace VerifyCmp

def SB : String := "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/verify/scratchbuild"
def CA : Name := `Ruliology.CellularAutomata

/-- scratch module, its olean path, catalog module -/
def moduleMap : List (Name × String × Name) :=
  [(`KC.Q01Lanes, "KC/Q01Lanes", CA ++ `Rule30ZeroBoundaryLanes)] ++
  ((List.range 16).map fun j =>
    (Name.mkStr `KC.Q01W52 s!"C{j}", s!"KC/Q01W52/C{j}",
     CA ++ Name.mkStr `Rule30Certificates s!"ZeroBoundaryWidth52Chunks{j / 4}")) ++
  [(`KC.Q01W52, "KC/Q01W52", CA ++ `Rule30ZeroBoundaryWidth52),
   (`KC.StripeFront, "KC/StripeFront", CA ++ `Rule30ZeroBoundaryStripeFront),
   (`KC.StripeCycles0, "KC/StripeCycles0", CA ++ `Rule30Certificates.ZeroBoundaryStripeCycles0),
   (`KC.StripeCycles1, "KC/StripeCycles1", CA ++ `Rule30Certificates.ZeroBoundaryStripeCycles1),
   (`KC.StripeCycles2, "KC/StripeCycles2", CA ++ `Rule30Certificates.ZeroBoundaryStripeCycles2),
   (`KC.StripeFamily, "KC/StripeFamily", CA ++ `Rule30ZeroBoundaryStripeFamily),
   (`KC.EtherTrap, "KC/EtherTrap", CA ++ `Rule30EtherTrap)] ++
  ((List.range 6).map fun k =>
    (Name.mkStr `KC s!"EtherTrapCerts{k}", s!"KC/EtherTrapCerts{k}",
     CA ++ Name.mkStr `Rule30Certificates s!"EtherTrap{k}")) ++
  [(`KC.EtherTrapMain, "KC/EtherTrapMain", CA ++ `Rule30EtherTrapWidth20),
   (`KC.PeriodTwoLang, "KC/PeriodTwoLang", CA ++ `Rule30PeriodTwoLanguage),
   (`KC.PeriodTwoW5, "KC/PeriodTwoW5", CA ++ `Rule30PeriodTwoWidth5),
   (`KC.PeriodTwoW6, "KC/PeriodTwoW6", CA ++ `Rule30PeriodTwoWidth6),
   (`P3Ether, "P3Ether", CA ++ `Rule30EtherThree),
   (`P3NoWall, "P3NoWall", CA ++ `Rule30EtherThreeNoWall),
   (`P3Trap001, "P3Trap001", CA ++ `Rule30EtherThreeTrap),
   (`P3Reach, "P3Reach", CA ++ `Rule30EtherThreeReach),
   (`P3Left, "P3Left", CA ++ `Rule30EtherThreeLeft),
   (`P3Skel, "P3Skel", CA ++ `Rule30EtherThreeSkeleton)]

/-- namespace prefix renaming for declaration names -/
def nsMap : List (Name × Name) :=
  [(`KC.Q01Lanes, CA ++ `Rule30ZeroBoundaryLanes),
   (`KC.Q01W52, CA ++ `Rule30ZeroBoundaryWidth52),
   (`KC.StripeFront, CA ++ `Rule30ZeroBoundaryStripeFront),
   (`KC.EtherTrap, CA ++ `Rule30EtherTrap),
   (`KC.PeriodTwoLang, CA ++ `Rule30PeriodTwoLanguage),
   (`KC.PeriodTwoW5, CA ++ `Rule30PeriodTwoWidth5),
   (`KC.PeriodTwoW6, CA ++ `Rule30PeriodTwoWidth6)]

def replacePrefix (n p q : Name) : Option Name :=
  if p.isPrefixOf n then some (n.replacePrefix p q) else none

/-- Rename a plain (non-private) name: a module-prefixed auxiliary name (`M._aux...`) uses the
module map; otherwise the longest matching namespace prefix. -/
def renamePlain (n : Name) : Name := Id.run do
  -- module-prefixed auxiliary names
  for (m, _, c) in moduleMap do
    if m.isPrefixOf n && n != m then
      let rest := (n.componentsRev.take (n.getNumParts - m.getNumParts)).reverse
      match rest.head? with
      | some (.str _ s) => if s.startsWith "_" then return n.replacePrefix m c
      | _ => pure ()
  let mut best : Option (Name × Name) := none
  for (p, q) in nsMap do
    if p.isPrefixOf n then
      match best with
      | some (p', _) => if p.getNumParts > p'.getNumParts then best := some (p, q)
      | none => best := some (p, q)
  match best with
  | some (p, q) => n.replacePrefix p q
  | none => n

/-- Rename, handling private names `_private.<module>.0.<decl>`. -/
def rename (n : Name) : Name := Id.run do
  let cs := n.components
  match cs with
  | (.str .anonymous "_private") :: rest =>
    -- split at the numeric component
    let idx := rest.findIdx? fun c => match c with | .num _ _ => true | _ => false
    match idx with
    | some i =>
      let modCs := rest.take i
      let numC := rest[i]!
      let declCs := rest.drop (i + 1)
      let mod := modCs.foldl (fun acc c => acc ++ c) Name.anonymous
      let decl := declCs.foldl (fun acc c => acc ++ c) Name.anonymous
      let mod' := match moduleMap.find? (fun (m, _, _) => m == mod) with
        | some (_, _, c) => c
        | none => mod
      let num := match numC with | .num _ k => k | _ => 0
      return (Name.mkNum (`_private ++ mod') num) ++ renamePlain decl
    | none => return renamePlain n
  | _ => return renamePlain n

def renameExpr (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .const n ls => some (.const (rename n) ls)
    | _ => none

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def hintsStr : ReducibilityHints → String
  | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => s!"regular {h}"

/-- Compare the non-proof data; returns a list of problems. `proofDiff` is set when only a theorem's
proof term differs. -/
def compareCI (s c : ConstantInfo) : List String × Bool := Id.run do
  let mut probs : List String := []
  let mut proofDiff := false
  if kindOf s != kindOf c then probs := s!"kind {kindOf s} vs {kindOf c}" :: probs
  if s.levelParams != c.levelParams then probs := "levelParams" :: probs
  if !(renameExpr s.type == c.type) then probs := "TYPE differs" :: probs
  match s, c with
  | .defnInfo a, .defnInfo b =>
    if !(renameExpr a.value == b.value) then probs := "DEF VALUE differs" :: probs
    if hintsStr a.hints != hintsStr b.hints then probs := s!"hints {hintsStr a.hints} vs {hintsStr b.hints}" :: probs
    if a.safety != b.safety then probs := "safety" :: probs
  | .thmInfo a, .thmInfo b =>
    if !(renameExpr a.value == b.value) then proofDiff := true
  | .opaqueInfo a, .opaqueInfo b =>
    if !(renameExpr a.value == b.value) then probs := "OPAQUE VALUE differs" :: probs
  | .inductInfo a, .inductInfo b =>
    if a.numParams != b.numParams || a.numIndices != b.numIndices || a.numNested != b.numNested ||
       a.isRec != b.isRec || a.isUnsafe != b.isUnsafe || a.isReflexive != b.isReflexive ||
       a.all.map rename != b.all || a.ctors.map rename != b.ctors then
      probs := "INDUCTIVE data differs" :: probs
  | .ctorInfo a, .ctorInfo b =>
    if rename a.induct != b.induct || a.cidx != b.cidx || a.numParams != b.numParams ||
       a.numFields != b.numFields || a.isUnsafe != b.isUnsafe then
      probs := "CTOR data differs" :: probs
  | .recInfo a, .recInfo b =>
    let rulesOk := a.rules.length == b.rules.length &&
      (a.rules.zip b.rules).all fun (r, r') =>
        rename r.ctor == r'.ctor && r.nfields == r'.nfields && renameExpr r.rhs == r'.rhs
    if a.all.map rename != b.all || a.numParams != b.numParams || a.numIndices != b.numIndices ||
       a.numMotives != b.numMotives || a.numMinors != b.numMinors || a.k != b.k ||
       a.isUnsafe != b.isUnsafe || !rulesOk then
      probs := "RECURSOR data differs" :: probs
  | .axiomInfo a, .axiomInfo b =>
    if a.isUnsafe != b.isUnsafe then probs := "axiom safety" :: probs
  | _, _ => pure ()
  return (probs, proofDiff)

end VerifyCmp

open VerifyCmp in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  let mut nCompared := 0
  let mut nProblems := 0
  let mut proofDiffs : Array Name := #[]
  let mut imageByCatMod : Std.HashMap Name NameSet := {}
  let mut nScratchByKind : Std.HashMap String Nat := {}
  for (sm, path, cm) in moduleMap do
    let (md, _region) ← readModuleData s!"{SB}/{path}.olean"
    let some cidx := env.getModuleIdx? cm | throwError "catalog module {cm} not loaded"
    for s in md.constants do
      nCompared := nCompared + 1
      nScratchByKind := nScratchByKind.insert (kindOf s) (nScratchByKind.getD (kindOf s) 0 + 1)
      let n' := rename s.name
      imageByCatMod := imageByCatMod.insert cm ((imageByCatMod.getD cm {}).insert n')
      match env.find? n' with
      | none =>
        nProblems := nProblems + 1
        lines := lines.push s!"MISSING in catalog: {s.name} -> {n'} (scratch module {sm})"
      | some c =>
        -- placement: the renamed constant must live in the mapped catalog module
        let placed := env.getModuleIdxFor? n'
        if placed != some cidx then
          nProblems := nProblems + 1
          lines := lines.push s!"WRONG MODULE: {n'} expected in {cm}"
        let (probs, pd) := compareCI s c
        if !probs.isEmpty then
          nProblems := nProblems + 1
          lines := lines.push s!"MISMATCH {s.name} -> {n'}: {probs}"
        if pd then
          proofDiffs := proofDiffs.push n'
  -- reverse direction: every constant of each catalog module is the image of a scratch constant
  let mut nExtra := 0
  let mut nCatalog := 0
  for (cm, img) in imageByCatMod.toList do
    let some cidx := env.getModuleIdx? cm | throwError "missing {cm}"
    for c in env.header.moduleData[cidx.toNat]!.constNames do
      nCatalog := nCatalog + 1
      if !img.contains c then
        nExtra := nExtra + 1
        lines := lines.push s!"EXTRA in catalog (no scratch counterpart): {c} in {cm}"
  lines := lines.push s!"proof-term differences (theorems; types identical): {proofDiffs}"
  IO.FS.writeFile "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/verify/compare_consts.txt"
    (String.intercalate "\n" lines.toList ++ "\n")
  logInfo m!"COMPARE: scratch constants {nCompared} (kinds {nScratchByKind.toList}); catalog constants \
    in mapped modules {nCatalog} in {imageByCatMod.size} modules; problems {nProblems}; extra {nExtra}; \
    theorem proof-term diffs {proofDiffs.size}: {proofDiffs}"
