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

open Lean Elab Command

-- t1: Q01 at width 52
-- t2: stripe-prefix family
-- t3: ether traps
-- t4: period 2
-- period 3

/-- The 28 new modules. -/
def newModules : List Name := [
  `Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks0,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks1,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks2,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks3,
  `Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52,
  `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles0,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles1,
  `Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles2,
  `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily,
  `Ruliology.CellularAutomata.Rule30EtherTrap,
  `Ruliology.CellularAutomata.Rule30Certificates.EtherTrap0,
  `Ruliology.CellularAutomata.Rule30Certificates.EtherTrap1,
  `Ruliology.CellularAutomata.Rule30Certificates.EtherTrap2,
  `Ruliology.CellularAutomata.Rule30Certificates.EtherTrap3,
  `Ruliology.CellularAutomata.Rule30Certificates.EtherTrap4,
  `Ruliology.CellularAutomata.Rule30Certificates.EtherTrap5,
  `Ruliology.CellularAutomata.Rule30EtherTrapWidth20,
  `Ruliology.CellularAutomata.Rule30PeriodTwoLanguage,
  `Ruliology.CellularAutomata.Rule30PeriodTwoWidth5,
  `Ruliology.CellularAutomata.Rule30PeriodTwoWidth6,
  `Ruliology.CellularAutomata.Rule30EtherThree,
  `Ruliology.CellularAutomata.Rule30EtherThreeNoWall,
  `Ruliology.CellularAutomata.Rule30EtherThreeTrap,
  `Ruliology.CellularAutomata.Rule30EtherThreeReach,
  `Ruliology.CellularAutomata.Rule30EtherThreeLeft,
  `Ruliology.CellularAutomata.Rule30EtherThreeSkeleton]


def nsPrefixes : List Name := [`Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes,
  `Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52, `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront,
  `Ruliology.CellularAutomata.Rule30EtherTrap, `Ruliology.CellularAutomata.Rule30PeriodTwoLanguage,
  `Ruliology.CellularAutomata.Rule30PeriodTwoWidth5, `Ruliology.CellularAutomata.Rule30PeriodTwoWidth6,
  `Ruliology.CellularAutomata.Rule30EtherThree]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array Name := #[]
  for m in newModules do
    let some idx := env.getModuleIdx? m | throwError "missing {m}"
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if !nsPrefixes.any (·.isPrefixOf c) then out := out.push c
  logInfo m!"OUTSIDE namespaces: {out.size}: {out.toList.take 30}"
