import Ruliology
import Lean
open Lean

def pairs : List (String × String × String) := [
  ("Ruliology.CellularAutomata.Rule30Prize", "Problem1", "Ruliology.CellularAutomata.Rule30Prize.Problem1"),
  ("Ruliology.CellularAutomata.Rule30Prize", "Problem2", "Ruliology.CellularAutomata.Rule30Prize.Problem2"),
  ("Ruliology.CellularAutomata.Rule30Prize", "no_column_eventually_constant", "Ruliology.CellularAutomata.Rule30Prize.no_column_eventually_constant"),
  ("Ruliology.CellularAutomata.Rule30Prize", "center_not_eventually_period_one", "Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_period_one"),
  ("Ruliology.CellularAutomata.Rule30Window", "no_small_eventual_period", "Ruliology.CellularAutomata.Rule30Window.no_small_eventual_period"),
  ("Ruliology.CellularAutomata.Rule30FactorWindow", "transient_add_period_ge", "Ruliology.CellularAutomata.Rule30FactorWindow.transient_add_period_ge"),
  ("Ruliology.CellularAutomata.Rule30BlackRuns", "nine_black", "Ruliology.CellularAutomata.Rule30BlackRuns.nine_black"),
  ("Ruliology.CellularAutomata.Rule30BlackRuns", "black_shield", "Ruliology.CellularAutomata.Rule30BlackRuns.black_shield"),
  ("Ruliology.CellularAutomata.Rule30BlackRuns", "no_long_black_run", "Ruliology.CellularAutomata.Rule30BlackRuns.no_long_black_run"),
  ("Ruliology.CellularAutomata.Rule30BlackRuns", "no_black_white_run", "Ruliology.CellularAutomata.Rule30BlackRuns.no_black_white_run"),
  ("Ruliology.CellularAutomata.Rule30BlackRuns", "not_eventually_zero_ones", "Ruliology.CellularAutomata.Rule30BlackRuns.not_eventually_zero_ones"),
  ("Ruliology.CellularAutomata.Rule30BlackRuns", "no_white_run_11", "Ruliology.CellularAutomata.Rule30BlackRuns.no_white_run_11"),
  ("Ruliology.CellularAutomata.Rule30BlackRunBlocks", "no_black_run_block", "Ruliology.CellularAutomata.Rule30BlackRunBlocks.no_black_run_block"),
  ("Ruliology.CellularAutomata.Rule30BlackRunBlocks", "no_period_black_run_then_white", "Ruliology.CellularAutomata.Rule30BlackRunBlocks.no_period_black_run_then_white"),
  ("Ruliology.CellularAutomata.Rule30StripCertificates", "problem1_iff_no_word", "Ruliology.CellularAutomata.Rule30StripCertificates.problem1_iff_no_word"),
  ("Ruliology.CellularAutomata.Rule30StripCertificates", "not_eventually_word_strip", "Ruliology.CellularAutomata.Rule30StripCertificates.not_eventually_word_strip"),
  ("Ruliology.CellularAutomata.Rule30StripCertificates", "Cert.sound", "Ruliology.CellularAutomata.Rule30StripCertificates.Cert.sound"),
  ("Ruliology.CellularAutomata.Rule30StripCertificates", "not_eventually_00000011", "Ruliology.CellularAutomata.Rule30StripCertificates.not_eventually_00000011"),
  ("Ruliology.CellularAutomata.Rule30StripCertificates", "not_eventually_000000000101", "Ruliology.CellularAutomata.Rule30StripCertificates.not_eventually_000000000101"),
  ("Ruliology.CellularAutomata.Rule30StripCertificateTable", "not_eventually_certTable", "Ruliology.CellularAutomata.Rule30StripCertificateTable.not_eventually_certTable"),
  ("Ruliology.CellularAutomata.Rule30Jen", "jen", "Ruliology.CellularAutomata.Rule30Jen.jen"),
  ("Ruliology.CellularAutomata.Rule30Jen", "periodic_column_unique", "Ruliology.CellularAutomata.Rule30Jen.periodic_column_unique"),
  ("Ruliology.CellularAutomata.Rule30Jen", "not_adjacent", "Ruliology.CellularAutomata.Rule30Jen.not_adjacent"),
  ("Ruliology.CellularAutomata.Rule30MaskedJen", "masked_jen", "Ruliology.CellularAutomata.Rule30MaskedJen.masked_jen"),
  ("Ruliology.CellularAutomata.Rule30MaskedJen", "orCol_not_eventuallyPeriodic", "Ruliology.CellularAutomata.Rule30MaskedJen.orCol_not_eventuallyPeriodic"),
  ("Ruliology.CellularAutomata.Rule30MaskedJen", "effective_step", "Ruliology.CellularAutomata.Rule30MaskedJen.effective_step"),
  ("Ruliology.CellularAutomata.Rule30MaskedJen", "window_jen", "Ruliology.CellularAutomata.Rule30MaskedJen.window_jen"),
  ("Ruliology.CellularAutomata.Rule30MaskedJen", "finitary_jen", "Ruliology.CellularAutomata.Rule30MaskedJen.finitary_jen"),
  ("Ruliology.CellularAutomata.Rule30DrivenLeft", "no_periodic_column", "Ruliology.CellularAutomata.Rule30DrivenLeft.no_periodic_column"),
  ("Ruliology.CellularAutomata.Rule30DrivenLeft", "barrier_exists", "Ruliology.CellularAutomata.Rule30DrivenLeft.barrier_exists"),
  ("Ruliology.CellularAutomata.Rule30DrivenLeft", "barrier_unique", "Ruliology.CellularAutomata.Rule30DrivenLeft.barrier_unique"),
  ("Ruliology.CellularAutomata.Rule30WhiteSeed", "problem1_black_or_white", "Ruliology.CellularAutomata.Rule30WhiteSeed.problem1_black_or_white"),
  ("Ruliology.CellularAutomata.Rule30WhiteSeed", "problem1_30_or_135", "Ruliology.CellularAutomata.Rule30WhiteSeed.problem1_30_or_135"),
  ("Ruliology.CellularAutomata.Rule30Diagonals", "R_periodic", "Ruliology.CellularAutomata.Rule30Diagonals.R_periodic"),
  ("Ruliology.CellularAutomata.Rule30Diagonals", "D_periodic", "Ruliology.CellularAutomata.Rule30Diagonals.D_periodic"),
  ("Ruliology.CellularAutomata.Rule30Diagonals", "center_eq_parity", "Ruliology.CellularAutomata.Rule30Diagonals.center_eq_parity"),
  ("Ruliology.CellularAutomata.Rule30RightPeriods", "e_step", "Ruliology.CellularAutomata.Rule30RightPeriods.e_step"),
  ("Ruliology.CellularAutomata.Rule30RightPeriods", "per_bound", "Ruliology.CellularAutomata.Rule30RightPeriods.per_bound"),
  ("Ruliology.CellularAutomata.Rule30RightPeriods", "per_upper", "Ruliology.CellularAutomata.Rule30RightPeriods.per_upper"),
  ("Ruliology.CellularAutomata.Rule30RightPeriods", "rows_at_powers_of_two", "Ruliology.CellularAutomata.Rule30RightPeriods.rows_at_powers_of_two"),
  ("Ruliology.CellularAutomata.Rule30RightPeriods", "not_half_lower", "Ruliology.CellularAutomata.Rule30RightPeriods.not_half_lower"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwo", "normalize", "Ruliology.CellularAutomata.Rule30PeriodTwo.normalize"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwo", "golden", "Ruliology.CellularAutomata.Rule30PeriodTwo.golden"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwo", "not_eventually_period_two_of_Q01", "Ruliology.CellularAutomata.Rule30PeriodTwo.not_eventually_period_two_of_Q01"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwo", "stripe_fixed", "Ruliology.CellularAutomata.Rule30PeriodTwo.stripe_fixed"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundary", "Q01_iff_Theta", "Ruliology.CellularAutomata.Rule30ZeroBoundary.Q01_iff_Theta"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundary", "Q01_iff_bounded", "Ruliology.CellularAutomata.Rule30ZeroBoundary.Q01_iff_bounded"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundary", "Q01_iff_staged", "Ruliology.CellularAutomata.Rule30ZeroBoundary.Q01_iff_staged"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundary", "count_constrained", "Ruliology.CellularAutomata.Rule30ZeroBoundary.count_constrained"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundary", "jen_clock", "Ruliology.CellularAutomata.Rule30ZeroBoundary.jen_clock"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundary", "free_bits_no00_no11111", "Ruliology.CellularAutomata.Rule30ZeroBoundary.free_bits_no00_no11111"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe", "stripe_absorb", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe.stripe_absorb"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe", "Theta_eventually_stripe_iff", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe.Theta_eventually_stripe_iff"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe", "first_defect_phase", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe.first_defect_phase"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundarySmall", "q01_width_le_16", "Ruliology.CellularAutomata.Rule30ZeroBoundarySmall.q01_width_le_16"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundarySmall", "q01_width_le_15_odd", "Ruliology.CellularAutomata.Rule30ZeroBoundarySmall.q01_width_le_15_odd"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes", "q01_of_checks", "Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.q01_of_checks"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes", "q01_of_chunks", "Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes.q01_of_chunks"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52", "q01_width_le_52", "Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52", "q01_width_le_52_linear", "Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.q01_width_le_52_linear"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52", "not_inX_of_width_le_52", "Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52.not_inX_of_width_le_52"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront", "front_sound", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.front_sound"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront", "family_of_class", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.family_of_class"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily", "stripe_prefix_family", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_prefix_family"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily", "stripe_prefix_family_list", "Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_prefix_family_list"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoCoupled", "CQ01_of_Q01", "Ruliology.CellularAutomata.Rule30PeriodTwoCoupled.CQ01_of_Q01"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoCoupled", "no_eventual_period_two_of_CQ01", "Ruliology.CellularAutomata.Rule30PeriodTwoCoupled.no_eventual_period_two_of_CQ01"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoCoupled", "ether_coupled_witness", "Ruliology.CellularAutomata.Rule30PeriodTwoCoupled.ether_coupled_witness"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoLanguage", "no_pattern", "Ruliology.CellularAutomata.Rule30PeriodTwoLanguage.no_pattern"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoWidth5", "col1_constraints", "Ruliology.CellularAutomata.Rule30PeriodTwoWidth5.col1_constraints"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoWidth5", "free_bit_constraints", "Ruliology.CellularAutomata.Rule30PeriodTwoWidth5.free_bit_constraints"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoWidth6", "col1_constraints", "Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.col1_constraints"),
  ("Ruliology.CellularAutomata.Rule30PeriodTwoWidth6", "free_bit_constraints", "Ruliology.CellularAutomata.Rule30PeriodTwoWidth6.free_bit_constraints"),
  ("Ruliology.CellularAutomata.Rule30Ether", "ether_rule", "Ruliology.CellularAutomata.Rule30Ether.ether_rule"),
  ("Ruliology.CellularAutomata.Rule30Ether", "trap_invariant", "Ruliology.CellularAutomata.Rule30Ether.trap_invariant"),
  ("Ruliology.CellularAutomata.Rule30Ether", "no_ether_wall_entry", "Ruliology.CellularAutomata.Rule30Ether.no_ether_wall_entry"),
  ("Ruliology.CellularAutomata.Rule30Ether", "absorption_excludes", "Ruliology.CellularAutomata.Rule30Ether.absorption_excludes"),
  ("Ruliology.CellularAutomata.Rule30Ether", "least_period_four_of_absorption", "Ruliology.CellularAutomata.Rule30Ether.least_period_four_of_absorption"),
  ("Ruliology.CellularAutomata.Rule30PeriodFourSkeleton", "skeleton_0001", "Ruliology.CellularAutomata.Rule30PeriodFourSkeleton.skeleton_0001"),
  ("Ruliology.CellularAutomata.Rule30PeriodFourSkeleton", "skeleton_0011", "Ruliology.CellularAutomata.Rule30PeriodFourSkeleton.skeleton_0011"),
  ("Ruliology.CellularAutomata.Rule30PeriodFourSkeleton", "column_m1_0111", "Ruliology.CellularAutomata.Rule30PeriodFourSkeleton.column_m1_0111"),
  ("Ruliology.CellularAutomata.Rule30PeriodFourSkeleton", "least_period_four_of_C3", "Ruliology.CellularAutomata.Rule30PeriodFourSkeleton.least_period_four_of_C3"),
  ("Ruliology.CellularAutomata.Rule30EtherTrap", "word_lemma", "Ruliology.CellularAutomata.Rule30EtherTrap.word_lemma"),
  ("Ruliology.CellularAutomata.Rule30EtherTrap", "escapes_of_certOK", "Ruliology.CellularAutomata.Rule30EtherTrap.escapes_of_certOK"),
  ("Ruliology.CellularAutomata.Rule30EtherTrap", "not_trap_of_certOK", "Ruliology.CellularAutomata.Rule30EtherTrap.not_trap_of_certOK"),
  ("Ruliology.CellularAutomata.Rule30EtherTrapWidth20", "pure_ether_not_in_trap_0001", "Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0001"),
  ("Ruliology.CellularAutomata.Rule30EtherTrapWidth20", "pure_ether_not_in_trap_0011", "Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0011"),
  ("Ruliology.CellularAutomata.Rule30EtherTrapWidth20", "pure_ether_not_in_trap_0111", "Ruliology.CellularAutomata.Rule30EtherTrap.pure_ether_not_in_trap_0111"),
  ("Ruliology.CellularAutomata.Rule30EtherThree", "ether3_rule", "Ruliology.CellularAutomata.Rule30EtherThree.ether3_rule"),
  ("Ruliology.CellularAutomata.Rule30EtherThree", "alignments_001_complete", "Ruliology.CellularAutomata.Rule30EtherThree.alignments_001_complete"),
  ("Ruliology.CellularAutomata.Rule30EtherThree", "alignments_011_complete", "Ruliology.CellularAutomata.Rule30EtherThree.alignments_011_complete"),
  ("Ruliology.CellularAutomata.Rule30EtherThree", "absorption3_excludes", "Ruliology.CellularAutomata.Rule30EtherThree.absorption3_excludes"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeNoWall", "no_wall_le_12", "Ruliology.CellularAutomata.Rule30EtherThree.no_wall_le_12"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeTrap", "trap_001", "Ruliology.CellularAutomata.Rule30EtherThree.trap_001"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeTrap", "absorptionT_excludes", "Ruliology.CellularAutomata.Rule30EtherThree.absorptionT_excludes"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeTrap", "not_eventually_001_of_absorption", "Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_absorption"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeReach", "t001_reached", "Ruliology.CellularAutomata.Rule30EtherThree.t001_reached"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeReach", "absorbed_empty", "Ruliology.CellularAutomata.Rule30EtherThree.absorbed_empty"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeLeft", "not_eventually_001_of_Q001", "Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_Q001"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeLeft", "not_eventually_011_of_C3w", "Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_011_of_C3w"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeLeft", "Q001_stripe", "Ruliology.CellularAutomata.Rule30EtherThree.Q001_stripe"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeLeft", "C3w_011_ether", "Ruliology.CellularAutomata.Rule30EtherThree.C3w_011_ether"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeSkeleton", "skeleton_001", "Ruliology.CellularAutomata.Rule30EtherThree.skeleton_001"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeSkeleton", "skeleton_011", "Ruliology.CellularAutomata.Rule30EtherThree.skeleton_011"),
  ("Ruliology.CellularAutomata.Rule30EtherThreeSkeleton", "not_eventually_001_of_C3s", "Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_C3s"),
  ("Ruliology.CellularAutomata.Rule30Realization", "column_realizable_unique", "Ruliology.CellularAutomata.Rule30Realization.column_realizable_unique"),
  ("Ruliology.CellularAutomata.Rule30Realization", "seed_perturbation", "Ruliology.CellularAutomata.Rule30Realization.seed_perturbation"),
  ("Ruliology.CellularAutomata.Rule30Realization", "barrier", "Ruliology.CellularAutomata.Rule30Realization.barrier"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers", "finite_abstraction_has_lasso", "Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers.finite_abstraction_has_lasso"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers", "no_local_ranking", "Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers.no_local_ranking"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers", "no_edge_dfa_ranking", "Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers.no_edge_dfa_ranking"),
  ("Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers", "no_joint_local_ranking", "Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers.no_joint_local_ranking"),
  ("Ruliology.CellularAutomata.Rule30Predecessors", "predCount_eq_three_iff", "Ruliology.CellularAutomata.Rule30.predCount_eq_three_iff"),
  ("Ruliology.CellularAutomata.Rule30Predecessors", "predCount_eq_one_iff", "Ruliology.CellularAutomata.Rule30.predCount_eq_one_iff"),
  ("Ruliology.CellularAutomata.Rule30PredecessorCounts", "sum_predCount", "Ruliology.CellularAutomata.Rule30.sum_predCount"),
  ("Ruliology.CellularAutomata.Rule30PredecessorCounts", "numWithPreds_zero", "Ruliology.CellularAutomata.Rule30.numWithPreds_zero"),
  ("Ruliology.CellularAutomata.Rule30Blocks", "blockAt_allowed", "Ruliology.CellularAutomata.Rule30Blocks.blockAt_allowed"),
  ("Ruliology.CellularAutomata.Rule30Blocks", "occurs_iff", "Ruliology.CellularAutomata.Rule30Blocks.occurs_iff"),
  ("Ruliology.CellularAutomata.Rule30Blocks", "occurs_single_cell", "Ruliology.CellularAutomata.Rule30Blocks.occurs_single_cell"),
  ("Ruliology.CellularAutomata.BusyBeaverLifetimes", "lifetime450504084", "Ruliology.CellularAutomata.BusyBeaverLifetimes.lifetime450504084"),
  ("Ruliology.CellularAutomata.BusyBeaverLifetimes", "lifetime5810255963295", "Ruliology.CellularAutomata.BusyBeaverLifetimes.lifetime5810255963295")
]

def nameEndsWith (n : Name) (suffix : List String) : Bool :=
  let comps := n.components.map (fun c => c.toString)
  comps.length ≥ suffix.length && comps.drop (comps.length - suffix.length) == suffix

#eval show CoreM Unit from do
  let env ← getEnv
  let mnames := env.header.moduleNames
  for (modStr, nm, fullStr) in pairs do
    let full := fullStr.toName
    let modName := modStr.toName
    let declMod : String := match env.getModuleIdxFor? full with
      | some idx => toString (mnames[idx.toNat]!)
      | none => "NONE"
    let exists_ := (env.find? full).isSome
    let kind : String := match env.find? full with
      | some (.thmInfo _) => "thm"
      | some (.defnInfo _) => "def"
      | some (.axiomInfo _) => "AXIOM"
      | some (.opaqueInfo _) => "opaque"
      | some (.inductInfo _) => "inductive"
      | some (.ctorInfo _) => "ctor"
      | some _ => "other"
      | none => "-"
    if exists_ && declMod == modStr then
      IO.println s!"OK   {fullStr} [{kind}]"
    else
      -- search the module for any constant ending with the given suffix
      let hits : Array Name := match env.getModuleIdx? modName with
        | some idx => (env.header.moduleData[idx.toNat]!).constNames.filter (fun c => nameEndsWith c (nm.splitOn "."))
        | none => #[]
      IO.println s!"BAD  {fullStr} exists={exists_} declMod={declMod} expectedMod={modStr} hitsInModule={hits.toList}"
