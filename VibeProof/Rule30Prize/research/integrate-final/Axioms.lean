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
import Lean

/-! Axiom check for the final-batch Rule 30 catalog modules (2026-10-15). Allowed: `propext`,
`Classical.choice`, `Quot.sound`. -/

-- Q01 for widths ≤ 52 (kernel-certify-r2 t1)
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.q01_of_checks
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.q01_of_chunks
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.run_sound
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.scanN_AD
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.scanN_lin
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.level
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.pat_spec
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.all_chunks
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52_linear
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.not_inX_of_width_le_52
-- stripe-prefix family (t2)
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_below
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.win_step
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.win_orb
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.sig_sound
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.seg_sound
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.front_sound
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.family_of_class
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_prefix_family
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_prefix_family_list
-- ether traps (t3)
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.word_lemma
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.escapes_of_certOK
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.not_trap_of_certOK
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.escapes_take
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.node_traj
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.escape_of_cert20
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_escapes_0001
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_escapes_0011
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_escapes_0111
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0001
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0011
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0111
-- period 2 (t4)
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoLanguage.no_pattern
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth5.col1_constraints
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth5.free_bit_constraints
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.col1_constraints
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.free_bit_constraints
-- period 3 (p3-ether)
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.ether3_rule
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.ether3_glide
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.alignments_001_complete
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.alignments_011_complete
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.trap_invariant3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.ether_wall_trap3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.no_ether_wall_entry3
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
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.absorbed_empty
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

/-! Sweep: every constant in the new namespaces, including all 256 chunk theorems and all
certificate checks, depends only on the allowed axioms. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let pres : List Name := [`Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes,
    `Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52,
    `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront,
    `Ruliology.CellularAutomata.Rule30EtherTrap,
    `Ruliology.CellularAutomata.Rule30PeriodTwoLanguage,
    `Ruliology.CellularAutomata.Rule30PeriodTwoWidth5,
    `Ruliology.CellularAutomata.Rule30PeriodTwoWidth6,
    `Ruliology.CellularAutomata.Rule30EtherThree]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold (fun (acc : Array Name) n _ =>
    if pres.any (·.isPrefixOf n) then acc.push n else acc) #[]
  let mut used : Array Name := #[]
  let mut bad : Array String := #[]
  for n in names do
    let axs ← collectAxioms n
    for a in axs do
      if !used.contains a then used := used.push a
      if !allowed.contains a then bad := bad.push s!"{n} uses {a}"
  IO.println s!"constants checked: {names.size}; axioms used: {used.toList}; violations: {bad.size}"
  for b in bad[:20] do IO.println b
