import Ruliology
import Lean

/-! Axiom check for the Rule 30 Prize Lean snapshot (`VibeProof/Rule30Prize/lean`, 2026-10-15).
Run from that folder: `lake env lean <this file>`. Allowed: `propext`, `Classical.choice`,
`Quot.sound`. -/

-- Period 1 (Rule30Prize)
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_period_one
#print axioms Ruliology.CellularAutomata.Rule30Prize.no_column_eventually_constant
-- Windows: no eventual period P ≤ 4096 with transient ≤ 8192; T + P ≥ 16359
#print axioms Ruliology.CellularAutomata.Rule30Window.no_small_eventual_period
#print axioms Ruliology.CellularAutomata.Rule30FactorWindow.transient_add_period_ge
-- Period 2: Q01 implies no eventual period 2; Q01 for every start of width ≤ 52
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwo.not_eventually_period_two_of_Q01
#print axioms Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52
-- Period 2, right half: free-bit constraints at strip width 6
#print axioms Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.free_bit_constraints
-- Least period 4: absorption excludes 0001, 0011, 0111; the pure ether is in no trap of width ≤ 20
#print axioms Ruliology.CellularAutomata.Rule30Ether.absorption_excludes
#print axioms Ruliology.CellularAutomata.Rule30Ether.least_period_four_of_absorption
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0001
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0011
#print axioms Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0111
-- Least period 3
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.no_wall_le_12
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_absorption
#print axioms Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_011_of_C3w

/-! Sweep: `Lean.collectAxioms` (the function behind `#print axioms`) for every constant declared
in any `Ruliology.*` module of the snapshot, including private and auxiliary constants. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.allImportedModuleNames
  let ours := mods.filter (fun m => (`Ruliology).isPrefixOf m)
  let names := env.constants.fold (fun (acc : Array Name) n _ =>
    match env.getModuleIdxFor? n with
    | some idx => if (`Ruliology).isPrefixOf (mods[idx.toNat]!) then acc.push n else acc
    | none => acc) #[]
  let mut used : Array Name := #[]
  let mut bad : Array String := #[]
  for n in names do
    for a in (← collectAxioms n) do
      unless used.contains a do used := used.push a
      unless allowed.contains a do bad := bad.push s!"{n} uses {a}"
  IO.println s!"sweep: {ours.size} Ruliology modules, {names.size} constants; axioms used: {used.toList}; violations: {bad.size}"
  for b in bad[:20] do IO.println b
