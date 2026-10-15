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
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52_linear
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.not_inX_of_width_le_52
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.all_chunks
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.run_sound
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.q01_of_checks
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.q01_of_chunks
-- t2: stripe-prefix family
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.win_step
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.front_sound
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.family_of_class
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_prefix_family
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_prefix_family_list
-- t3: ether traps
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.word_lemma
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.escapes_of_certOK
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.escapes_take
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.node_traj
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_escapes_0001
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_escapes_0011
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_escapes_0111
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0001
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0011
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0111
-- t4: period 2
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoLanguage.no_pattern
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth5.col1_constraints
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth5.free_bit_constraints
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.col1_constraints
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.free_bit_constraints
-- period 3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.ether3_rule
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.ether3_glide
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.alignments_001_complete
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.alignments_011_complete
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.trap_invariant3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.ether_wall_trap3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.absorption3_excludes
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_absorption3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_011_of_absorption3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.wallOK_lift
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.wallOK_back
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.no_wall_le_12
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.PTrap.invariant
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.PTrap.trap
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.absorptionT_excludes
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.t001_check
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.trap_001
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_absorption
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.t001_reached
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.col_m1_001
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.col_m1_011
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_Q001
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.Q001_stripe
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_011_of_C3w
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.C3w_011_ether
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.skeleton_001
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.skeleton_011
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.col_m1_001_skeleton
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_C3s

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

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

-- Sweep: every constant of every new module.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut kinds : Std.HashMap String Nat := {}
  let mut violations : Array (Name × Array Name) := #[]
  let mut flagged : Array Name := #[]
  let mut union : NameSet := {}
  for m in newModules do
    let some idx := env.getModuleIdx? m | throwError "module {m} not loaded"
    let data := env.header.moduleData[idx.toNat]!
    for c in data.constNames do
      total := total + 1
      let some ci := env.find? c | throwError "missing constant {c}"
      kinds := kinds.insert (kindOf ci) (kinds.getD (kindOf ci) 0 + 1)
      let isPartialDef := match ci with
        | .defnInfo d => d.safety != .safe
        | _ => false
      if ci.isUnsafe || isPartialDef || isExtern env c ||
          (Compiler.implementedByAttr.getParam? env c).isSome ||
          (match ci with | .axiomInfo _ => true | .opaqueInfo _ => true | _ => false) then
        flagged := flagged.push c
      let axs ← collectAxioms c
      for a in axs do union := union.insert a
      if axs.any (fun a => !allowedAxioms.contains a) then
        violations := violations.push (c, axs)
  logInfo m!"SWEEP: {total} constants in {newModules.length} modules; kinds {kinds.toList}; \
    axioms used (union): {union.toList}; flagged (axiom/opaque/unsafe/partial/extern/implemented_by): \
    {flagged}; violations: {violations.size} {violations}"
