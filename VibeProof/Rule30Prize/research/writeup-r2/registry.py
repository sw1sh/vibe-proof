"""Theorem registry for rule30-state.html.

Every entry is a Lean declaration whose axioms were re-printed in this pass (outputs in ax/).
Fields: key, file id, Lean name (as printed in the axiom output), kind, statement (plain text,
`backticks` for code), and for kind 'impl' the open hypothesis.
kind: 'thm'    proved theorem (hypotheses, if any, are part of the statement)
      'kernel' proved by a kernel-checked finite computation (decide / decide +kernel)
      'impl'   proved implication whose hypothesis is OPEN (named in `hyp`)
"""
R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/'
MAIN = '/Users/swish/src/wolfram/vibe-proof/ruliology-lean/Ruliology/CellularAutomata/'
STG = R + 'staging/Ruliology/CellularAutomata/'

# file id -> (display path, absolute path, axiom-output file, name prefix used in the output)
FILES = {
    'JEN':  ('ruliology-lean/Ruliology/CellularAutomata/Rule30Jen.lean', MAIN + 'Rule30Jen.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30Jen.'),
    'PRIZE': ('ruliology-lean/Ruliology/CellularAutomata/Rule30Prize.lean', MAIN + 'Rule30Prize.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30Prize.'),
    'DIAG': ('ruliology-lean/Ruliology/CellularAutomata/Rule30Diagonals.lean', MAIN + 'Rule30Diagonals.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30Diagonals.'),
    'WIN':  ('ruliology-lean/Ruliology/CellularAutomata/Rule30Window.lean', MAIN + 'Rule30Window.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30Window.'),
    'FW':   ('staging/Ruliology/CellularAutomata/Rule30FactorWindow.lean', STG + 'Rule30FactorWindow.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30FactorWindow.'),
    'MJ':   ('staging/Ruliology/CellularAutomata/Rule30MaskedJen.lean', STG + 'Rule30MaskedJen.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30MaskedJen.'),
    'BR':   ('staging/Ruliology/CellularAutomata/Rule30BlackRuns.lean', STG + 'Rule30BlackRuns.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30BlackRuns.'),
    'BRB':  ('staging/Ruliology/CellularAutomata/Rule30BlackRunBlocks.lean', STG + 'Rule30BlackRunBlocks.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30BlackRunBlocks.'),
    'SC':   ('staging/Ruliology/CellularAutomata/Rule30StripCertificates.lean', STG + 'Rule30StripCertificates.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30StripCertificates.'),
    'SCT':  ('staging/Ruliology/CellularAutomata/Rule30StripCertificateTable.lean', STG + 'Rule30StripCertificateTable.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30StripCertificateTable.'),
    'WS':   ('staging/Ruliology/CellularAutomata/Rule30WhiteSeed.lean', STG + 'Rule30WhiteSeed.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30WhiteSeed.'),
    'DL':   ('staging/Ruliology/CellularAutomata/Rule30DrivenLeft.lean', STG + 'Rule30DrivenLeft.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30DrivenLeft.'),
    'RP':   ('staging/Ruliology/CellularAutomata/Rule30RightPeriods.lean', STG + 'Rule30RightPeriods.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30RightPeriods.'),
    'RZ':   ('staging/Ruliology/CellularAutomata/Rule30Realization.lean', STG + 'Rule30Realization.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30Realization.'),
    'P2':   ('staging/Ruliology/CellularAutomata/Rule30PeriodTwo.lean', STG + 'Rule30PeriodTwo.lean', 'ax_r1.out', 'Ruliology.CellularAutomata.Rule30PeriodTwo.'),
    'CORE': ('progA-backdet/lean/ZBLCore.lean', R + 'progA-backdet/lean/ZBLCore.lean', 'chk_ZBLCore.out', 'R30ProgA.'),
    'MONO': ('A-monovariant/lean/ZBL.lean', R + 'A-monovariant/lean/ZBL.lean', 'chk_ZBLmono.out', 'ZBL.'),
    'SUPP': ('V-A2-epochs-rigor/Supp.lean', R + 'V-A2-epochs-rigor/Supp.lean', 'chk_Supp.out', 'ZBL.'),
    'RECON': ('A-reconmap/lean/ZBL.lean', R + 'A-reconmap/lean/ZBL.lean', 'chk_ZBLrecon.out', 'R30ZBL.'),
    'RCHK': ('verify-A2-reconmap-rigor/ZBLcheck.lean', R + 'verify-A2-reconmap-rigor/ZBLcheck.lean', 'chk_ZBLcheck.out', 'R30ZBL.'),
    'A1':   ('verify-A1reform-rigor/A1Reform.lean', R + 'verify-A1reform-rigor/A1Reform.lean', 'chk_A1Reform.out', 'A1ReformCheck.'),
    'BAR':  ('A-invsearch/lean/ZBLBarrier.lean', R + 'A-invsearch/lean/ZBLBarrier.lean', 'chk_ZBLBarrier.out', 'ZBLBarrier.'),
    'COR':  ('verify-A2-rigor/ZBLBarrierCorollary.lean', R + 'verify-A2-rigor/ZBLBarrierCorollary.lean', 'chk_Corollary.out', 'ZBLBarrier.'),
    'JB':   ('A-invsearch/lean/JointBarrier.lean', R + 'A-invsearch/lean/JointBarrier.lean', 'chk_JointBarrier.out', 'JointBarrier.'),
    'DFA':  ('A-invsearch/lean/ZBLEdgeDFA.lean', R + 'A-invsearch/lean/ZBLEdgeDFA.lean', 'chk_EdgeDFA.out', 'ZBLEdgeDFA.'),
    'EW':   ('B-edge-trap/lean/EtherWall.lean', R + 'B-edge-trap/lean/EtherWall.lean', 'chk_EtherWall.out', 'R30EtherWall.'),
    'SK1':  ('progB-avoid/lean/Skel0001.lean', R + 'progB-avoid/lean/Skel0001.lean', 'chk_Skel0001.out', 'R30Skel.'),
    'SK3':  ('progB-avoid/lean/Skel0011.lean', R + 'progB-avoid/lean/Skel0011.lean', 'chk_Skel0011.out', 'R30Skel.'),
    'DSK':  ('verify-b2-rigor/DirectSkel0011.lean', R + 'verify-b2-rigor/DirectSkel0011.lean', 'chk_DirectSkel0011.out', 'VerifyB2.'),
    # deduplicated modules staged by the integration task after round 2; compiled from source in this pass
    'ZB':   ('staging/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean', STG + 'Rule30ZeroBoundary.lean', 'ax_r2_staged.out', 'Ruliology.CellularAutomata.Rule30ZeroBoundary.'),
    'ZBS':  ('staging/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripe.lean', STG + 'Rule30ZeroBoundaryStripe.lean', 'ax_r2_staged.out', 'Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe.'),
    'P4S':  ('staging/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean', STG + 'Rule30PeriodFourSkeleton.lean', 'ax_r2_staged.out', 'Ruliology.CellularAutomata.Rule30PeriodFourSkeleton.'),
    'P2C':  ('staging/Ruliology/CellularAutomata/Rule30PeriodTwoCoupled.lean', STG + 'Rule30PeriodTwoCoupled.lean', 'ax_r2_staged.out', 'Ruliology.CellularAutomata.Rule30PeriodTwoCoupled.'),
}

# (section id, section title) in table order
SECTIONS = [
    ('s2-jen', '2.1 Jen and constant columns'),
    ('s2-diag', '2.2 Diagonal periods'),
    ('s2-win', '2.3 Window bounds'),
    ('s2-mj', '2.4 Masked Jen and the effective boundary'),
    ('s2-br', '2.5 Nine-black shield and black runs'),
    ('s2-sc', '2.6 Strip-certificate word exclusions'),
    ('s2-ws', '2.7 White seed and rule 135'),
    ('s3-p2', '3.1 Period 2'),
    ('s3-p4', '3.2 Least period 4 and absorption'),
    ('s3-c3', '3.3 Least period 4 and C3'),
    ('s4-real', '4.1 ZBL realization and conjugacy'),
    ('s4-clock', '4.2 Jen with a clock'),
    ('s4-epoch', '4.3 Epochs'),
    ('s4-stripe', '4.4 Stripe stability and absorption'),
    ('s4-small', '4.5 Kernel width checks'),
    ('s4-ether', '4.6 Ether and the W109 wall'),
    ('s4-skel', '4.7 Skeletons'),
    ('s4-dl', '4.8 Driven left half'),
    ('s4-rp', '4.9 Right-diagonal period theory'),
    ('s5-q01', '5.1 Q01-only barriers'),
    ('s5-joint', '5.2 Two-sided JointBarrier'),
    ('s5-edge', '5.3 Edge-region and realization barriers'),
    ('s7', '7.1 Refutations of the single-trap claim'),
]

T = []
def add(sec, key, fid, name, kind, stmt, hyp=None):
    T.append(dict(sec=sec, key=key, fid=fid, name=name, kind=kind, stmt=stmt, hyp=hyp))

# ---------------------------------------------------------------- 2.1
s = 's2-jen'
add(s, 'left_edge', 'JEN', 'cell_left_edge', 'thm', 'Left edge: `cell t (-t) = 1`.')
add(s, 'left_white', 'JEN', 'cell_eq_false_of_lt', 'thm', '`cell t p = 0` for `p < -t`.')
add(s, 'cell_left', 'JEN', 'cell_left', 'thm', 'Left permutivity: `cell t (i-1) = cell (t+1) i ⊕ (cell t i ∨ cell t (i+1))`.')
add(s, 'periodic_left_all', 'JEN', 'periodic_left_all', 'thm', 'If columns i and i+1 both have period P from time T, every column to their left has period P from T.')
add(s, 'no_left_periodic', 'JEN', 'no_left_periodic', 'thm', 'The columns i, i-1, i-2, … cannot all have period P from T (the left edge reaches each of them once).')
add(s, 'between_periodic', 'JEN', 'between_periodic', 'thm', 'If columns j and k > j+1 are eventually periodic, so is column j+1 (pigeonhole on the strip between them).')
add(s, 'not_adjacent', 'JEN', 'not_adjacent', 'thm', 'Two adjacent columns are never both eventually periodic.')
add(s, 'jen', 'JEN', 'jen', 'thm', 'Jen (1986): two different columns are never both eventually periodic.')
add(s, 'periodic_column_unique', 'JEN', 'periodic_column_unique', 'thm', 'At most one column is eventually periodic.')
add(s, 'no_column_const', 'PRIZE', 'no_column_eventually_constant', 'thm', 'No column is eventually constant, for any transient.')
add(s, 'center_not_const', 'PRIZE', 'center_not_eventually_constant', 'thm', 'The center column is not eventually constant.')
add(s, 'center_not_p1', 'PRIZE', 'center_not_eventually_period_one', 'thm', 'No N with `c(t+1) = c(t)` for all t ≥ N: Problem 1 for period 1.')
# ---------------------------------------------------------------- 2.2
s = 's2-diag'
add(s, 'center_eq_R', 'DIAG', 'center_eq_R', 'thm', '`c(t) = R_t(t)` where `R_j(t) = cell t (t-j)`.')
add(s, 'center_eq_D', 'DIAG', 'center_eq_D', 'thm', '`c(t) = D_t(t)` where `D_j(t) = cell t (j-t)`.')
add(s, 'R_zero', 'DIAG', 'R_zero', 'thm', 'The right edge is black: `R_0(t) = 1` for all t.')
add(s, 'R_step', 'DIAG', 'R_step', 'thm', '`R_{j+2}(t+1) = R_{j+2}(t) ⊕ (R_{j+1}(t) ∨ R_j(t))`.')
add(s, 'D_step', 'DIAG', 'D_step', 'thm', '`D_{j+2}(t+1) = D_j(t) ⊕ (D_{j+1}(t) ∨ D_{j+2}(t))`.')
add(s, 'R_periodic', 'DIAG', 'R_periodic', 'thm', 'Every right diagonal is periodic from t = 0 with period 2^j.')
add(s, 'D_periodic', 'DIAG', 'D_periodic', 'thm', 'Every left diagonal is eventually periodic with period 2^j.')
add(s, 'center_eq_parity', 'DIAG', 'center_eq_parity', 'thm', 'For t ≥ 2, c(t) is the parity of #{s < t : cell s (s-t+1) ∨ cell s (s-t+2)}.')
# ---------------------------------------------------------------- 2.3
s = 's2-win'
add(s, 'row_testBit', 'WIN', 'row_testBit', 'thm', 'Packed rows (three bit operations per step) agree with `cell` for t ≤ K.')
add(s, 'centerLoop_spec', 'WIN', 'centerLoop_spec', 'thm', 'Specification of the kernel loop that records the center bits.')
add(s, 'center_eq_bit', 'WIN', 'center_eq_bit', 'kernel', '`c(t)` equals bit t of the kernel-computed constant `centerBits` for t < 16384.')
add(s, 'witnessCheck_true', 'WIN', 'witnessCheck_true', 'kernel', 'Every P ≤ 4096 is broken by a witness in [8192, 8224).')
add(s, 'no_small_eventual_period', 'WIN', 'no_small_eventual_period', 'thm', 'No eventual period 0 < P ≤ 4096 with transient T ≤ 8192.')
add(s, 'win_inj', 'FW', 'win_inj', 'kernel', 'The 16359 factors of length 26 of c starting at 0, …, 16358 are pairwise distinct.')
add(s, 'transient_add_period_ge', 'FW', 'transient_add_period_ge', 'thm', 'If `c(t+P) = c(t)` for all t ≥ T with P > 0, then T + P ≥ 16359.')
# ---------------------------------------------------------------- 2.4
s = 's2-mj'
add(s, 'left_of_black', 'MJ', 'left_of_black', 'thm', 'Where column i is black, `cell t (i-1) = ¬cell (t+1) i`.')
add(s, 'left_of_white', 'MJ', 'left_of_white', 'thm', 'Where column i is white, `cell t (i-1) = cell (t+1) i ⊕ cell t (i+1)`.')
add(s, 'masked_jen', 'MJ', 'masked_jen', 'thm', 'Masked Jen: if column i has period P from T, column i+1 is not P-periodic from T on the white times of column i.')
add(s, 'masked_jen_center', 'MJ', 'masked_jen_center', 'thm', 'Masked Jen at the center, with any later start T′.')
add(s, 'center_masked', 'MJ', 'center_masked_not_eventually_periodic', 'thm', 'The pair (c(t), column 1 at the white times of c) is not eventually periodic.')
add(s, 'orCol', 'MJ', 'orCol_not_eventuallyPeriodic', 'thm', 'If column i is eventually periodic, `orCol i = column i ∨ column i+1` is not.')
add(s, 'effective_boundary', 'MJ', 'effective_boundary', 'thm', 'Effective boundary: `cell t (-1) ∨ c(t) = cell t (-1) ∨ (c(t) ∧ c(t+1))`.')
add(s, 'effective_step', 'MJ', 'effective_step', 'thm', 'Column -1 evolves with `c(t) ∧ c(t+1)` in place of `c(t)`.')
add(s, 'determine', 'MJ', 'determine', 'thm', 'Determination: agreement of column i and orCol i on a window propagates to columns i-k on a triangle.')
add(s, 'window_jen', 'MJ', 'window_jen', 'thm', 'Window Jen: two times t₁ < t₂ never carry the same (center, orCol 0) window of length t₂.')
add(s, 'window_jen_col', 'MJ', 'window_jen_col', 'thm', 'The window form for any column i.')
add(s, 'periodic_window', 'MJ', 'periodic_window', 'thm', 'If c has period P from T, every [n, 2n) with n ≥ T+P contains a white center time where column 1 breaks period P.')
add(s, 'finitary_jen', 'MJ', 'finitary_jen', 'thm', 'For 0 < P ≤ n, c and orCol 0 are never both P-periodic on all of [n-P, 2n].')
# ---------------------------------------------------------------- 2.5
s = 's2-br'
add(s, 'nine_black_core', 'BR', 'nine_black_core', 'kernel', 'Finite core of Lemma A: all 2^11 rows of columns m+1..m+11.')
add(s, 'eight_black_not_enough', 'BR', 'eight_black_not_enough', 'thm', 'Eight black steps do not suffice for this light-cone argument (explicit row).')
add(s, 'nine_black', 'BR', 'nine_black', 'thm', 'Lemma A: column m black at t, …, t+8 forces `cell (t+9) (m+1) = 0` and `cell (t+9) (m+2) = 1`.')
add(s, 'black_shield', 'BR', 'black_shield', 'thm', 'Lemma A*: column m black for 9j steps forces (white black)^j in columns m+1..m+2j right after.')
add(s, 'long_runs_col', 'BR', 'not_eventuallyPeriodic_of_long_one_runs_col', 'thm', 'A column whose black runs followed by white all have length ≥ 9 (from some time) is not eventually periodic.')
add(s, 'long_runs', 'BR', 'not_eventuallyPeriodic_of_long_one_runs', 'thm', 'The same for the center column.')
add(s, 'finitary_long_runs', 'BR', 'finitary_long_runs', 'thm', 'Finitary long-runs theorem on [a, 2n] with n ≥ a + 2P + 10.')
add(s, 'zero_ones', 'BR', 'not_eventually_zero_ones', 'thm', 'c is never eventually `(0 1^k)^∞` for k ≥ 9.')
add(s, 'thmB', 'BR', 'no_long_black_run', 'thm', 'Theorem B: a period P cannot contain a black run of length r with 9⌈(P-r+9)/2⌉ ≤ r.')
add(s, 'thmD', 'BR', 'no_black_white_run', 'thm', 'Theorem D: a period cannot contain a black run s ≥ 9 followed by a white run r ≥ 1 + 9⌈(k+8)/2⌉, k = P-s-r.')
add(s, 'white_run_11', 'BR', 'no_white_run_11', 'thm', 'c is never eventually `(0^r 1 1)^∞` for r ≥ 10.')
add(s, 'thmBprime', 'BRB', 'no_black_run_block', 'thm', 'Theorem B′: if `Determined u j0` holds, c is never eventually `(1^r u)^∞` with r ≥ max(9, 9 j0).')
for nm, w in [('det_0', '0'), ('det_00', '00'), ('det_000', '000'), ('det_0000', '0000'), ('det_0100', '0100'), ('det_010', '010'), ('det_0010', '0010'), ('det_0110', '0110')]:
    add(s, nm, 'BRB', nm, 'kernel', f'`Determined` holds for u = {w} (j0 = {"2" if nm in ("det_0","det_00","det_000","det_0000","det_0100") else "3"}).')
add(s, 'black_run_then_white', 'BRB', 'no_period_black_run_then_white', 'thm', 'c is never eventually `(1^r 0)^∞` for r ≥ 18.')
# ---------------------------------------------------------------- 2.6
s = 's2-sc'
add(s, 'problem1_iff_no_word', 'SC', 'problem1_iff_no_word', 'thm', 'Problem1 ⟺ no nonempty word w has `EventuallyWord w` (c = w^∞ from some time).')
add(s, 'word_strip', 'SC', 'not_eventually_word_strip', 'thm', 'Soundness of bitmask strip certificates: `stripCert w K k` ⇒ ¬EventuallyWord w.')
add(s, 'w01111111', 'SC', 'not_eventually_01111111', 'thm', '`0 1^7` is excluded (bitmask certificate, width 5).')
add(s, 'iterG_period', 'SC', 'Cert.iterG_period', 'thm', 'The counter-phase map of a rank certificate returns after m·P steps.')
add(s, 'Cert_sound', 'SC', 'Cert.sound', 'thm', 'Soundness of rank certificates: passing checks ⇒ c is not eventually w^∞ (any phase).')
add(s, 'Cert_word', 'SC', 'Cert.not_eventuallyWord', 'thm', 'The same, stated with EventuallyWord.')
add(s, 'w00000011', 'SC', 'not_eventually_00000011', 'thm', '`0^6 1 1` is excluded (rank certificate, width 6, 379 ranks).')
add(s, 'w000000000101', 'SC', 'not_eventually_000000000101', 'thm', '`0^9 1 0 1` is excluded (rank certificate, width 7, 1309 ranks).')
add(s, 'certTable_ok', 'SCT', 'certTable_ok', 'kernel', 'All 30 bitmask certificates of `certTable` pass.')
add(s, 'certTable', 'SCT', 'not_eventually_certTable', 'thm', 'Each of the 30 table words (lengths 8 to 13) is excluded.')
# ---------------------------------------------------------------- 2.7
s = 's2-ws'
add(s, 'cellW_succ', 'WS', 'cellW_succ', 'thm', 'Rule 30 from one white cell on black: `cellW (t+1) p = cell t (p-1)`.')
add(s, 'cell135_succ', 'WS', 'cell135_succ', 'thm', 'Rule 135 from one black cell: `cell135 (t+1) p = ¬cell t (p-1)`.')
add(s, 'black_or_white', 'WS', 'problem1_black_or_white', 'thm', 'The black-seed and white-seed center columns of rule 30 are not both eventually periodic.')
add(s, 'r30_or_135', 'WS', 'problem1_30_or_135', 'thm', 'The single-seed center columns of rules 30 and 135 are not both eventually periodic.')
# ---------------------------------------------------------------- 3.1
s = 's3-p2'
add(s, 'normalize', 'P2', 'normalize', 'thm', 'If `c(t+2) = c(t)` for t ≥ T₀, then c alternates from some T: black at T+2k, white at T+2k+1.')
add(s, 'm1_even', 'P2', 'm1_even', 'thm', 'If c alternates from T (black first), column -1 is black at every T+2k.')
add(s, 'p1_odd', 'P2', 'p1_odd', 'thm', 'Under alternation, `cell (T+2k+1) 1 = ¬cell (T+2k+1) (-1)`.')
add(s, 'm2_even', 'P2', 'm2_even', 'thm', 'Under alternation, column -2 at T+2k is ¬(column -1 at T+2k+1).')
add(s, 'm2_odd', 'P2', 'm2_odd', 'thm', 'Under alternation, column -2 at odd offsets is a function of the free bits.')
add(s, 'm3_even', 'P2', 'm3_even', 'thm', 'Under alternation, column -3 at even offsets is a function of the free bits.')
add(s, 'm3_odd', 'P2', 'm3_odd', 'thm', 'Under alternation, `cell (T+2k+1) (-3) = cell (T+2k+3) (-1)`.')
add(s, 'golden', 'P2', 'golden', 'thm', 'Under alternation, the free bits `cell (T+2k+1) (-1)` never have two consecutive zeros.')
add(s, 'm4_odd', 'P2', 'm4_odd', 'thm', 'Under alternation, column -4 is white at every T+2k+1.')
add(s, 'no_AA', 'P2', 'no_AA', 'kernel', 'With c = 0101 on [t, t+3], column 1 never reads 0000 there.')
add(s, 'no_BB', 'P2', 'no_BB', 'kernel', 'With c = 0101 on [t, t+3], column 1 never reads 0101 there.')
add(s, 'no_ABAB', 'P2', 'no_ABAB', 'kernel', 'With c = 01010101 on [t, t+7], column 1 never reads 00010001 there.')
add(s, 'col4_white_of_alt', 'P2', 'col4_white_of_alt', 'thm', 'With c = 0,1,0,1,0 on [t, t+4], column -4 is white at t.')
add(s, 'effective_white', 'P2', 'effective_white', 'thm', 'Under alternation the effective boundary c(t) ∧ c(t+1) is white.')
add(s, 'left_half_zero_driven', 'P2', 'left_half_zero_driven', 'thm', 'Under alternation from T, the left half from T on is the zero-boundary left half (ZBL) started from the row at T.')
add(s, 'p2_of_Q01', 'P2', 'not_eventually_period_two_of_Q01', 'impl', 'Q01 ⇒ the center column is not eventually 2-periodic, for every transient.', 'Rule30PeriodTwo.Q01')
add(s, 'stripe_fixed_p2', 'P2', 'stripe_fixed', 'thm', 'The infinite stripe (black at odd positions < 0) is fixed by the ZBL.')
add(s, 'stripe_col', 'P2', 'stripe_col', 'thm', 'From the infinite stripe, column -1 is black at every step: finiteness in Q01 is essential.')
add(s, 'left_half_is_zbl', 'CORE', 'left_half_is_zbl', 'thm', 'While c(t) ∧ c(t+1) is white, the left half evolves as the ZBL (index i ↔ position -(i+1)).')
add(s, 'core_effective_boundary', 'CORE', 'effective_boundary', 'thm', 'Effective boundary (second proof, ZBLCore encoding).')
add(s, 'L_eq_zorb', 'CORE', 'L_eq_zorb', 'thm', 'Bridge: the staged driven left half with white driver equals `zorb` up to re-indexing.')
add(s, 'Q01_iff_LR', 'CORE', 'Q01_iff_LR', 'thm', 'Q01 ⟺ LR: for every choice of free bits f the forced row `lam (alt f)` is infinite.')
add(s, 'Q01_iff_bounded', 'CORE', 'Q01_iff_bounded', 'thm', 'Q01 ⟺ BWR: ∀d ∃B ∀f, the forced row has a black cell in [d, d+B) (via compactness).')
add(s, 'Q01_iff_staged', 'CORE', 'Q01_iff_staged', 'thm', 'R30ProgA.Q01 ⟺ the staged Rule30PeriodTwo.Q01.')
add(s, 'Q01_phase1', 'CORE', 'Q01_phase1', 'impl', 'Q01 ⇒ the phase-1 version (column -1 black at every odd step) also fails for finite rows.', 'R30ProgA.Q01')
add(s, 'uniform_death', 'CORE', 'uniform_death', 'impl', 'Q01 ⇒ for each support bound d a common time D by which every row supported in [0, d) has died.', 'R30ProgA.Q01')
add(s, 'no_eventual_period_two', 'CORE', 'no_eventual_period_two', 'impl', 'Q01 ⇒ no eventual period 2 (second proof).', 'R30ProgA.Q01')
add(s, 'left_right_white', 'CORE', 'left_right_white', 'thm', 'At a white center time followed by a black one, `cell t 1 = ¬cell t (-1)`.')
add(s, 'cell_m1_step_of_noBB', 'RECON', 'cell_m1_step_of_noBB', 'thm', 'If c(t) ∧ c(t+1) = 0, column -1 updates as if column 0 were white.')
add(s, 'cell_eq_zrow', 'RECON', 'cell_eq_zrow', 'thm', 'The left half is the ZBL `zrow` while c(t) ∧ c(t+1) = 0 (third encoding).')
add(s, 'recon_m1_black', 'RECON', 'm1_black', 'thm', 'If c(t) = 1 and c(t+1) = 0 then column -1 is black at t.')
add(s, 'no_period_two_of_Q01', 'RECON', 'no_period_two_of_Q01', 'impl', 'Q01 (zrow form) ⇒ no eventual period 2 (third proof).', 'R30ZBL.Q01')
add(s, 'Q01_iff_Phi', 'RECON', 'Q01_iff_Phi', 'thm', 'Q01 ⟺ for every f, the reconstruction Φ(f) is not finitely supported.')
add(s, 'part_c1', 'A1', 'part_c1', 'thm', 'Q01 in its general reading (either phase, any start time) ⟺ Θ(f) is never finite.')
add(s, 'koenig', 'A1', 'koenig', 'thm', 'König: some f has Θ(f) of width ≤ W ⟺ every depth of the search tree is nonempty.')
add(s, 'FW_closed', 'A1', 'FW_closed', 'thm', '{f : Θ(f) has width ≤ W} is closed in the product topology.')
add(s, 'zb_Q01_iff_Theta', 'ZB', 'Q01_iff_Theta', 'thm', 'Unified encoding: Q01 ⟺ no Θ(f) is finitely supported.')
add(s, 'zb_Q01_any_phase', 'ZB', 'Q01_iff_any_phase', 'thm', 'Q01 ⟺ no finite start keeps column -1 black at T, T+2, T+4, … for any T.')
add(s, 'zb_Q01_iff_staged', 'ZB', 'Q01_iff_staged', 'thm', 'The unified Q01 is the staged Rule30PeriodTwo.Q01.')
add(s, 'col1_black_among_five', 'ZB', 'col1_black_among_five', 'kernel', 'If c alternates black-first from T, column 1 is black at one of any five consecutive white steps (light-cone check over columns 1..11).')
add(s, 'no00_no11111', 'ZB', 'free_bits_no00_no11111', 'thm', 'Under alternation the free bits contain neither 00 nor 11111.')
add(s, 'CQ01_of_Q01', 'P2C', 'CQ01_of_Q01', 'impl', 'Q01 ⇒ CQ01.', 'Rule30ZeroBoundary.Q01')
add(s, 'p2_of_CQ01', 'P2C', 'no_eventual_period_two_of_CQ01', 'impl', 'CQ01 ⇒ the center column is not eventually 2-periodic, for every transient.', 'Rule30PeriodTwoCoupled.CQ01')
# ---------------------------------------------------------------- 3.2
s = 's3-p4'
add(s, 'cell_eq_drv', 'EW', 'cell_eq_drv', 'thm', 'From time T on, the true right half is the right half driven by c from the row at T.')
add(s, 'absorption_excludes', 'EW', 'absorption_excludes', 'impl', 'Absorption(w, A) with aligned A ⇒ c is never eventually w^∞.', 'R30EtherWall.Absorption w A')
add(s, 'A0001_ok', 'EW', 'A0001_ok', 'kernel', 'Alignments A0001 = [(5,0), (6,0)] are valid.')
add(s, 'A0011_ok', 'EW', 'A0011_ok', 'kernel', 'Alignments A0011 = [(0,0), (1,3), (4,0)] are valid.')
add(s, 'A0111_ok', 'EW', 'A0111_ok', 'kernel', 'Alignment A0111 = [(2,2)] is valid.')
add(s, 'lp4_absorption', 'EW', 'least_period_four_of_absorption', 'impl', 'Absorption for 0001, 0011 and 0111 ⇒ c is not eventually any rotation of these words (no least period 4).', 'Absorption w0001 A0001 ∧ Absorption w0011 A0011 ∧ Absorption w0111 A0111')
# ---------------------------------------------------------------- 3.3
s = 's3-c3'
add(s, 'not_tail_of_C3', 'P4S', 'not_tail_of_C3', 'impl', 'C3 w, a w-periodic tail and an eventual fit of column -1 to P_w are contradictory.', 'Rule30PeriodFourSkeleton.C3 w')
add(s, 'n0001_of_C3', 'P4S', 'not_eventually_0001_of_C3', 'impl', 'C3(0001) ⇒ c is never eventually (0001)^∞.', 'C3 w0001')
add(s, 'n0011_of_C3', 'P4S', 'not_eventually_0011_of_C3', 'impl', 'C3(0011) ⇒ c is never eventually (0011)^∞.', 'C3 w0011')
add(s, 'n0111_of_C3', 'P4S', 'not_eventually_0111_of_C3', 'impl', 'C3(0111) ⇒ c is never eventually (0111)^∞.', 'C3 w0111')
add(s, 'lp4_C3', 'P4S', 'least_period_four_of_C3', 'impl', 'C3 for 0001, 0011 and 0111 ⇒ c has no least period 4, for every transient.', 'C3 w0001 ∧ C3 w0011 ∧ C3 w0111')
# ---------------------------------------------------------------- 4.1
s = 's4-real'
add(s, 'backward_det', 'CORE', 'backward_det', 'thm', 'Two rows with the same image and the same wall-adjacent cell are equal.')
add(s, 'history_det', 'CORE', 'history_det', 'thm', 'A history is determined by its last row and the wall-adjacent cells before it.')
add(s, 'back_fin_iff', 'CORE', 'back_fin_iff', 'thm', 'Finite-preimage criterion via the backward transducer.')
add(s, 'zorb_edge', 'CORE', 'zorb_edge', 'thm', 'The leftmost black cell of a ZBL row moves out one cell per step.')
add(s, 'core_light_cone', 'CORE', 'light_cone', 'thm', 'Light cone of the ZBL.')
add(s, 'col_light_cone', 'CORE', 'col_light_cone', 'thm', 'Column -1 up to time m-1 depends only on the first m cells.')
add(s, 'pivot', 'CORE', 'pivot', 'thm', 'Pivot: rows agreeing on [0, t) and differing at t have different wall-adjacent cells at time t.')
add(s, 'zero_run_local', 'CORE', 'zero_run_local', 'thm', 'A white run [d, d+L) in the row localizes column -1 up to time d+L-1.')
add(s, 'realize', 'CORE', 'realize', 'thm', 'The sideways reconstruction `cols a` reproduces the ZBL orbit of `lam a`.')
add(s, 'realization', 'CORE', 'realization', 'thm', 'Realization bijection: each column -1 sequence a comes from exactly one ZBL row, `lam a`.')
add(s, 'two_step_shift', 'CORE', 'two_step_shift', 'thm', 'Conjugacy: two ZBL steps of `lam (alt f)` give `lam (alt (shift f))`.')
add(s, 'survive_iff', 'CORE', 'survive_iff', 'thm', 'At a forced black step, the next forced step is black iff cells 2 and 3 differ.')
add(s, 'col2_doubling', 'CORE', 'col2_doubling', 'thm', 'Column -2 is constant on each surviving forced pair of steps.')
add(s, 'col3_of_col2', 'CORE', 'col3_of_col2', 'thm', 'Column -3 is the complement of column -2 one step later (when -1, -2 are not both white).')
add(s, 'no_two_white', 'CORE', 'no_two_white', 'thm', 'Constrained histories have no 00 in columns -1, -2 at both steps of a forced pair.')
add(s, 'zrow_det', 'RECON', 'zrow_det', 'thm', 'Trace determination: position k at time t depends only on column -1 at times t, …, t+k-1.')
add(s, 'zrow_pivot', 'RECON', 'zrow_pivot', 'thm', 'Pivot structure: L(k+1) = y_k ⊕ (function of y_0..y_{k-1}).')
add(s, 'zrow_recon', 'RECON', 'zrow_recon', 'thm', 'The sideways reconstruction `recon` is the ZBL orbit.')
add(s, 'trace_surj', 'RECON', 'trace_surj', 'thm', 'Every boundary column is the trace of some ZBL row.')
add(s, 'Phi_inX', 'RECON', 'Phi_inX', 'thm', 'Φ(f) satisfies the period-2 constraint.')
add(s, 'Phi_free', 'RECON', 'Phi_free', 'thm', 'The free bits of Φ(f) are f.')
add(s, 'small_identities', 'RECON', 'small_identities', 'thm', 'Constrained rows: L2 = ¬f₀, L3 = f₀, L4 = ¬f₁, L5 = f₀.')
add(s, 'V_Phi_unique', 'RCHK', 'V_Phi_unique', 'thm', 'A constrained row with free bits f equals Φ(f) at every depth k ≥ 1.')
add(s, 'V_d_even', 'RCHK', 'V_d_even', 'thm', 'Φ(f)(2s+2) = f_s ⊕ g_s(f_0..f_{s-1}).')
add(s, 'V_d_odd', 'RCHK', 'V_d_odd', 'thm', 'Φ(f)(2s+3) depends only on f_0..f_s.')
add(s, 'V_d_pivot_flip', 'RCHK', 'V_d_pivot_flip', 'thm', 'Flipping only f_s flips Φ(f)(2s+2).')
add(s, 'V_F2_Phi', 'RCHK', 'V_F2_Phi', 'thm', 'F² ∘ Φ = Φ ∘ shift (third proof of the conjugacy).')
add(s, 'part_a', 'A1', 'part_a', 'thm', 'A wall-respecting row is constrained ⟺ it equals Θ(f) for some f.')
add(s, 'Theta_inj', 'A1', 'Theta_inj', 'thm', 'Θ is injective.')
add(s, 'tri_even_form', 'A1', 'tri_even_form', 'thm', 'Θ(f)(2j+2) = ¬f_j ⊕ G(f_0..f_{j-1}).')
add(s, 'tri_odd_form', 'A1', 'tri_odd_form', 'thm', 'Θ(f)(2j+1) depends only on f_0..f_{j-1}.')
add(s, 'equivariance', 'A1', 'equivariance', 'thm', 'Z² ∘ Θ = Θ ∘ σ.')
add(s, 'S_closed', 'A1', 'S_closed', 'thm', 'The image of Θ is closed.')
add(s, 'inverse_dep', 'A1', 'inverse_dep', 'thm', 'f_s is determined by Θ(f) at depths ≤ 2s+2 (continuous inverse).')
add(s, 'part_d', 'A1', 'part_d', 'thm', 'Exactly 2^⌊W/2⌋ rows of width ≤ W satisfy the constraint at every even t ≤ W-1.')
add(s, 'row_is_list', 'A1', 'row_is_list', 'thm', 'Every wall-respecting row of width ≤ W is `toRow l` for a list l of length W.')
add(s, 'toRow_inj', 'A1', 'toRow_inj', 'thm', '`toRow` is injective on lists of equal length.')
add(s, 'count_constrained', 'ZB', 'count_constrained', 'thm', 'Unified encoding of part_d: exactly 2^⌊W/2⌋ constrained starts of width ≤ W up to time W-1.')
# ---------------------------------------------------------------- 4.2
s = 's4-clock'
add(s, 'jen_clock', 'CORE', 'jen_clock', 'thm', 'Jen with a clock: if column -1 of a finite ZBL row (edge at m-1) is P-periodic on [T, T+L], then L+2 ≤ T+m+2P.')
add(s, 'col_not_ep', 'CORE', 'col_not_eventually_periodic', 'thm', 'Column -1 of a nonzero finite ZBL row is never eventually periodic.')
add(s, 'free_bits_clock', 'CORE', 'free_bits_clock', 'thm', 'Under the constraint, a p-periodic stretch of free bits from s₀ has length ℓ with 2ℓ+2 ≤ 2s₀+m+4p.')
add(s, 'alt_free_clock', 'CORE', 'alternating_free_bits_clock', 'thm', 'For rule 30 with c alternating from T: column -1 at white times is not p-periodic on long windows.')
add(s, 'alt_right_clock', 'CORE', 'alternating_right_col1_clock', 'thm', 'The same for column 1 at the white times (interface to the right half).')
add(s, 'all_columns_periodic', 'MONO', 'all_columns_periodic', 'thm', 'In the ZBL, a periodic column 1 makes every column periodic.')
add(s, 'col1_periodic_white', 'MONO', 'col1_periodic_white', 'thm', 'Jen for the ZBL: for a finite start, an eventually periodic column 1 is eventually white.')
add(s, 'constrained_col1_aperiodic', 'MONO', 'constrained_col1_aperiodic', 'thm', 'Under the constraint, column 1 of a finite start is not eventually periodic.')
add(s, 'col1_not_eventually_true', 'MONO', 'col1_not_eventually_true', 'thm', 'For a finite start, column 1 is not eventually black (free bits not eventually 1).')
add(s, 'alt_col_neg1_aperiodic', 'MONO', 'alt_col_neg1_aperiodic', 'thm', 'If c alternates (Alt T), column -1 of rule 30 is not eventually periodic.')
add(s, 'trace_not_ep', 'RECON', 'trace_not_eventuallyPeriodic', 'thm', 'The boundary column of a nonzero finite ZBL row is not eventually periodic.')
add(s, 'free_not_ep', 'RECON', 'free_not_eventuallyPeriodic', 'thm', 'A finite constrained row has free bits that are not eventually periodic.')
# ---------------------------------------------------------------- 4.3
s = 's4-epoch'
add(s, 'step_s', 'MONO', 'step_s', 'thm', 'The stripe s (black at odd depths) is a fixed point of the ZBL.')
add(s, 'inv_step', 'MONO', 'inv_step', 'thm', 'Left-permutive inversion inside the ZBL.')
add(s, 'first_defect_step', 'MONO', 'first_defect_step', 'thm', 'The first deviation from the stripe moves one cell toward the wall per step.')
add(s, 'first_defect_run', 'MONO', 'first_defect_run', 'thm', 'Iterated form: the first deviation reaches depth 1 at speed one.')
add(s, 'first_defect_hits', 'MONO', 'first_defect_hits', 'thm', 'A first deviation at depth d turns depth 1 white at time d-1.')
add(s, 'first_defect_even', 'MONO', 'first_defect_even', 'thm', 'In a constrained history the first deviation (reached in time) is at an even depth.')
add(s, 'first_defect_parity', 'MONO', 'first_defect_parity', 'thm', 'At any time t, the first deviation depth d satisfies t+d even.')
add(s, 'free_bit', 'MONO', 'free_bit', 'thm', 'If depth 1 is black, the next depth-1 value is ¬(depth 2).')
add(s, 'reset_config', 'MONO', 'reset_config', 'thm', 'Configuration at a reset: 0, 1, s₃, …, s_d, then a deviation at depth d+1.')
add(s, 'alt_left_run', 'MONO', 'alt_left_run', 'thm', 'Bridge: under Alt T (white first) the left half of rule 30 is a ZBL orbit.')
add(s, 'alt_constrained', 'MONO', 'alt_constrained', 'thm', 'Under Alt T, the left half from T+1 satisfies the phase-0 constraint.')
add(s, 'alt_first_defect_parity', 'MONO', 'alt_first_defect_parity', 'thm', 'Under Alt T (c(T) = 0), at time T+1+t the first deviation depth d has t+d even.')
add(s, 'free_bit_iff', 'SUPP', 'free_bit_iff', 'thm', 'With depth 1 black: the free bit is 0 ⟺ the first deviation is at depth 2.')
add(s, 'epoch_col1', 'SUPP', 'epoch_col1', 'thm', 'An epoch: a first deviation at depth d at time a keeps depth 1 black on [a, a+d-2], white at a+d-1.')
add(s, 'epoch_survives_iff', 'SUPP', 'epoch_survives_iff', 'thm', 'An epoch starting at an even time satisfies the constraint ⟺ its depth d is even.')
add(s, 'after_reset', 'SUPP', 'after_reset', 'thm', 'After a reset at odd τ with next depth d: d even, d ≥ 2, free bits 1 at τ+2, …, τ+d-2 and 0 at τ+d.')
add(s, 'alt_first_defect_phase', 'SUPP', 'alt_first_defect_phase', 'thm', 'Phase-free bridge: under Alt T, at u ≥ T+1 the first deviation depth is even ⟺ c(u) = 1.')
add(s, 'alt_other_phase', 'SUPP', 'alt_other_phase', 'thm', 'Under Alt (T+1) the parity reverses: the one-phase reading of the prose is false for the other phase.')
add(s, 'first_defect_phase', 'ZBS', 'first_defect_phase', 'thm', 'Unified phase-free form: under black-first alternation from T, at every u ≥ T the first deviation depth is even ⟺ c(u) = 1.')
# ---------------------------------------------------------------- 4.4
s = 's4-stripe'
add(s, 'agrees_two_steps', 'MONO', 'agrees_two_steps', 'thm', 'If x equals the stripe from depth L ≥ 1, so does Z²x.')
add(s, 'agrees_run_even', 'MONO', 'agrees_run_even', 'thm', 'The same after any even number of steps.')
add(s, 'agrees_pre', 'MONO', 'agrees_pre', 'thm', 'If Z y equals the stripe from L, then y equals it from L+4.')
add(s, 'agrees_pre_run', 'MONO', 'agrees_pre_run', 'thm', 'If Z^t x equals the stripe from L, then x equals it from L+4t.')
add(s, 'finite_never_stripe', 'MONO', 'finite_never_stripe', 'thm', 'A finitely supported row never becomes stripe-tailed.')
add(s, 'recon_stripe_fixed', 'RECON', 'stripe_fixed', 'thm', 'The stripe is a fixed point (zrow encoding).')
add(s, 'stripe_confined', 'RECON', 'stripe_confined', 'thm', 'Agreement with the stripe from an odd position K persists at all later times.')
add(s, 'stripe_tail_trace_periodic', 'RECON', 'stripe_tail_trace_periodic', 'thm', 'A stripe-tailed row has an eventually periodic boundary column.')
add(s, 'front_check', 'RECON', 'front_check', 'kernel', 'Front check over the 2^12 contents of cells 1..12 (stripe from 13): cells 11, 12 become 1, 0 within 9 steps.')
add(s, 'small_check', 'RECON', 'small_check', 'kernel', 'Every content of cells 1..10 (stripe from 11) reaches the stripe within 40 steps.')
add(s, 'front_advance', 'RECON', 'front_advance', 'thm', 'With stripe agreement from an odd m ≥ 13, within 9 steps it holds from m-2.')
add(s, 'stripe_absorb', 'RECON', 'stripe_absorb', 'thm', 'A row agreeing with the stripe from an odd position becomes exactly the stripe and stays.')
add(s, 'stripe_tail_one', 'RECON', 'stripe_tail_free_eventually_one', 'thm', 'Hence its column -1 is eventually black (free bits eventually 1).')
add(s, 'stripe2_fixed', 'RECON', 'stripe2_fixed', 'thm', 'The even-phase stripe (black at even positions) satisfies the ZBL rule away from the wall.')
add(s, 'stripe2_confined', 'RECON', 'stripe2_confined', 'thm', 'Even-phase stripe agreement from an even K ≥ 2 persists.')
add(s, 'front_check2', 'RECON', 'front_check2', 'kernel', 'Even-phase front check over 2^13 contents.')
add(s, 'small_check2', 'RECON', 'small_check2', 'kernel', 'Even-phase small-strip check over 2^11 contents.')
add(s, 'front_advance2', 'RECON', 'front_advance2', 'thm', 'Even-phase front advance (m ≥ 14).')
add(s, 'stripe2_absorb', 'RECON', 'stripe2_absorb', 'thm', 'Even-phase absorption on depths ≥ 2; depth 1 then alternates.')
add(s, 'stripe2_tail_zero', 'RECON', 'stripe2_tail_free_eventually_zero', 'thm', 'A constrained row with an even-phase stripe tail has free bits eventually 0.')
add(s, 'Theta_eventually_stripe_iff', 'ZBS', 'Theta_eventually_stripe_iff', 'thm', 'Θ(f) agrees with the stripe beyond some depth ⟺ f is eventually 1.')
# ---------------------------------------------------------------- 4.5
s = 's4-small'
add(s, 'check_16', 'MONO', 'check_16', 'kernel', 'Packed exhaustive check `checkBelow 34 (2^16)`.')
add(s, 'q01_width_le_16', 'MONO', 'q01_width_le_16', 'thm', 'Q01 for every row of width ≤ 16: depth 1 is white at some even time < 34.')
add(s, 'q01_width_le_15_odd', 'MONO', 'q01_width_le_15_odd', 'thm', 'The odd phase for width ≤ 15.')
add(s, 'not_alt_small', 'MONO', 'not_alt_small', 'thm', 'The center column cannot alternate (white first) from any T ≤ 15 (consistency check of the bridge).')
# ---------------------------------------------------------------- 4.6
s = 's4-ether'
add(s, 'ether_rule', 'EW', 'ether_rule', 'thm', 'The 7×4 ether table is a rule-30 orbit.')
add(s, 'ether_period', 'EW', 'ether_period', 'thm', 'The ether has temporal period 4.')
for nm, txt in [('aligned_0001_5', '0001 = ether column 5 (c)'), ('aligned_0001_6', '0001 = ether column 6'), ('aligned_0011_0', '0011 = ether column 0 (B1)'),
                ('aligned_0011_1', '0011 = ether column 1 (B2) shifted by 3'), ('aligned_0011_4', '0011 = ether column 4 (B5)'), ('aligned_0111_2', '0111 = ether column 2 (B3) shifted by 2'),
                ('aligned_0101_3', '0101 = ether column 3 (B4)')]:
    add(s, nm, 'EW', nm, 'kernel', f'Alignment: {txt}.')
add(s, 'wallOK_true', 'EW', 'wallOK_true', 'kernel', 'The 109 wall states are closed under every right input and carry B4 next to a white B3.')
add(s, 'wall_facts', 'EW', 'wall_facts', 'thm', 'Unpacked wall properties.')
add(s, 'trap_invariant', 'EW', 'trap_invariant', 'thm', 'Ether on columns 1..k (k a B3) plus a wall state on k+1..k+13 persists forever.')
add(s, 'ether_wall_trap', 'EW', 'ether_wall_trap', 'thm', 'If c is an ether column from T and the true row enters the family at t₁ ≥ T: contradiction (masked Jen).')
add(s, 'no_ether_wall_entry', 'EW', 'no_ether_wall_entry', 'thm', 'For aligned w: if c = w^∞ from T, the true right half never enters the ether+wall family.')
add(s, 'config_finite', 'EW', 'config_finite', 'thm', 'The explicit configurations `config` are finitely supported.')
add(s, 'config_pure_ether', 'EW', 'config_pure_ether', 'thm', 'Driven by aligned w, `config` keeps columns 1..b pure ether forever.')
add(s, 'pure_not_in_S0001', 'EW', 'pure_not_in_S0001', 'kernel', 'Pure ether rows are not in the round-1 trap S0001.')
add(s, 'pure_not_in_S0011', 'EW', 'pure_not_in_S0011', 'kernel', 'Pure ether rows are not in S0011.')
add(s, 'pure_not_in_S0111', 'EW', 'pure_not_in_S0111', 'kernel', 'Pure ether rows are not in S0111.')
add(s, 'evol_c7_four', 'JB', 'evol_c7_four', 'thm', 'c7 (black at p ≡ 6 mod 7) returns after 4 steps.')
add(s, 'evol_c7_period', 'JB', 'evol_c7_period', 'thm', 'The c7 orbit has temporal period 4.')
add(s, 'c7_center', 'JB', 'c7_center', 'thm', 'Column 0 of the c7 orbit alternates.')
add(s, 'tr_agree', 'JB', 'tr_agree', 'thm', 'The finite truncation of c7 to [-(7N+1), 7N+6] agrees with c7 inside the shrinking cone.')
add(s, 'c7_ether_check', 'P2C', 'c7_ether_check', 'kernel', 'Decide check: the c7 orbit equals the ether table on one period (shift 4).')
add(s, 'c7_eq_ether', 'P2C', 'c7_eq_ether', 'thm', 'Column j+4 of the c7 orbit is ether column j at every time.')
add(s, 'ether_check', 'P2C', 'ether_check', 'kernel', 'B3 is black wherever B4 is; B4 alternates; B3 and B5 at the even phases.')
add(s, 'B4_imp_B3', 'P2C', 'B4_imp_B3', 'thm', 'B3 is black wherever B4 is black.')
add(s, 'altCol_eq_B4', 'P2C', 'altCol_eq_B4', 'thm', 'The alternating column is B4, one phase later.')
add(s, 'etherLeft_zbl', 'P2C', 'etherLeft_zbl', 'thm', 'The ether’s left half is a ZBL orbit (a white wall in place of B4 changes nothing).')
add(s, 'ether_col1_black', 'P2C', 'ether_col1_black', 'thm', 'Column -1 of the ether’s left half is black at the black steps.')
add(s, 'ether_free_bits', 'P2C', 'ether_free_bits', 'thm', 'Its free bits alternate 0, 1, 0, 1, …')
add(s, 'etherLeft_eq_Theta', 'P2C', 'etherLeft_eq_Theta', 'thm', 'The ether’s left half is Θ of the alternating free bits.')
add(s, 'etherRight_drv', 'P2C', 'etherRight_drv', 'thm', 'The ether’s right half is the right half driven by the alternating column.')
add(s, 'ether_coupled_witness', 'P2C', 'ether_coupled_witness', 'thm', 'The ether satisfies every condition of CQ01 except finite support.')
# ---------------------------------------------------------------- 4.7
s = 's4-skel'
add(s, 'sk1_Cert_sound', 'SK1', 'Cert.sound', 'thm', 'Rank-certificate soundness (copy used by the skeleton files).')
add(s, 'sk1_sound_bad', 'SK1', 'Cert.sound_bad', 'thm', 'If c = w^∞, the true strip eventually stays in the designated bad class.')
add(s, 'sk1_eventually_pred', 'SK1', 'Cert.eventually_pred', 'thm', 'Every predicate checked on the bad class holds eventually along the true history.')
add(s, 'K0001_checkb', 'SK1', 'K0001_checkb', 'kernel', 'Certificate checks for 0001 (width-b strips).')
add(s, 'K0001_checkGb', 'SK1', 'K0001_checkGb', 'kernel', 'Counter checks for 0001.')
add(s, 'K0001_badImp', 'SK1', 'K0001_badImp', 'kernel', 'The bad class of 0001 implies the skeleton predicate.')
add(s, 'skeleton_0001', 'SK1', 'skeleton_0001', 'thm', 'If c = (0001)^∞ from T: eventually col1 = 0, col3 = 1 at phase 0; col2 = 1 at phase 1; col1 = 1 at phase 2; col1 = 1, col2 = 0 at phase 3.')
add(s, 'skeleton_0001_explicit', 'SK1', 'skeleton_0001_explicit', 'thm', 'Adds column -1: eventually (0, = col1, 0, 1) at phases (0, 1, 2, 3).')
add(s, 'no11check_true', 'SK1', 'no11check_true', 'kernel', 'Finite check behind no11_0001.')
add(s, 'no11_0001', 'SK1', 'no11_0001', 'thm', 'If c = (0001)^∞ from T: eventually, at phase 1, a black column-1 cell is followed 4 steps later by a white one (free bits have no 11).')
add(s, 'sk3_sound_bad', 'SK3', 'Cert.sound_bad', 'thm', 'Bad-class soundness (copy in the 0011 file).')
add(s, 'sk3_eventually_pred', 'SK3', 'Cert.eventually_pred', 'thm', 'Eventual predicate (copy in the 0011 file).')
add(s, 'K0011_checkb', 'SK3', 'K0011_checkb', 'kernel', 'Certificate checks for 0011.')
add(s, 'K0011_checkGb', 'SK3', 'K0011_checkGb', 'kernel', 'Counter checks for 0011.')
add(s, 'K0011_badImp', 'SK3', 'K0011_badImp', 'kernel', 'The bad class of 0011 implies the skeleton predicate.')
add(s, 'skeleton_0011', 'SK3', 'skeleton_0011', 'thm', 'If c = (0011)^∞ from T: eventually column 1 is black at phases 1, 2 and white at phase 3.')
add(s, 'skeleton_0011_explicit', 'SK3', 'skeleton_0011_explicit', 'thm', 'Adds column -1: eventually (= col1, 0, 0, 1) at phases (0, 1, 2, 3).')
add(s, 'column_m1_0111', 'SK3', 'column_m1_0111', 'thm', 'If c = (0111)^∞ from T: for all t ≥ T, column -1 is (= ¬col1, 0, 0, 1) at phases (0, 1, 2, 3).')
add(s, 'direct_skel', 'DSK', 'skel', 'thm', 'Independent re-proof of skeleton_0011_explicit by a hand argument, without certificates.')
# ---------------------------------------------------------------- 4.8
s = 's4-dl'
add(s, 'dl_edge', 'DL', 'edge', 'thm', 'In the driven left half from a finite nonzero start, the leftmost black cell moves left one cell per step, for any driver.')
add(s, 'dl_adjacent', 'DL', 'no_periodic_adjacent', 'thm', 'Two adjacent columns i, i+1 ≤ 0 of the driven left half are never both eventually periodic.')
add(s, 'dl_col_neg_one', 'DL', 'col_neg_one_not_periodic', 'thm', 'With an eventually periodic driver, column -1 of the driven left half is not eventually periodic.')
add(s, 'dl_no_periodic_column', 'DL', 'no_periodic_column', 'thm', 'With an eventually periodic driver, no column q < 0 of the driven left half is eventually periodic.')
add(s, 'dl_cell_eq_L', 'DL', 'cell_eq_L', 'thm', 'From time T on, the real left half is the half driven by the real center column.')
add(s, 'dl_cell_eq_L_eff', 'DL', 'cell_eq_L_effective', 'thm', 'From time T on, the real left half is the half driven by the effective boundary c(T+k) ∧ c(T+k+1).')
add(s, 'dl_light_cone', 'DL', 'light_cone', 'thm', 'Light cone of the driven left half.')
add(s, 'dl_permutive', 'DL', 'permutive', 'thm', 'Flipping start cell -(k+1) flips column -1 at step k.')
add(s, 'dl_ones_fails', 'DL', 'ones_fails', 'thm', 'With driver ≡ 1, every finite start makes column -1 black at some step ≤ n+1.')
# ---------------------------------------------------------------- 4.9
s = 's4-rp'
for nm, txt in [
    ('per_mono_all', 'If R_{j+1} has period H, so does every R_i, i ≤ j.'),
    ('e_mono', 'e_j ≤ e_{j+1} (e_j = least e with R_j of period 2^e).'),
    ('shift_formula', 'If R_j has period H: R_{j+1}(t+H) = R_{j+1}(t) ⊕ R_{j+1}(H).'),
    ('per_succ_iff', 'Doubling criterion: given period H on R_j, R_{j+1} keeps it ⟺ R_{j+1}(H) = 0.'),
    ('antiperiod', 'When the period doubles, a shift by H complements R_{j+1}.'),
    ('half_black', 'When the period doubles, every window of one period is exactly half black.'),
    ('e_step', 'e_{j+1} = e_j + [R_{j+1}(2^{e_j}) = 1].'),
    ('S_rule', 'e_j − e_{j−1} is the parity of the black input cells over one input period (j ≥ 3).'),
    ('inp_least_period', 'Every period of the input of diagonal j is a multiple of 2^{e_{j−1}}.'),
    ('no_three', 'The period never doubles three times in a row.'),
    ('period_gt', 'Every period of R_j (j ≥ 1) exceeds ⌈j/2⌉.'),
    ('not_per_small', 'R_j does not have period 2^k when 2^{k+1} ≤ j; periods are unbounded.'),
    ('per_bound', 'A diagonal of period 2^k has index ≤ 2^{k+1} − 2.'),
    ('per_upper', 'e_j ≤ ⌊(2j+1)/3⌋ for j ≥ 2.'),
    ('per_14', 'R_14 has period 2^6 (row 64 ends in 1 preceded by 14 whites).'),
    ('per_23', 'R_23 has period 2^8.'),
    ('not_half_lower', 'The guess e_j ≥ ⌊j/2⌋ is false.'),
    ('per_iff_gap', 'R_n has period 2^k ⟺ row 2^k has n white cells left of its right edge.'),
    ('rows_at_powers_of_two', 'Rows at powers of two: the diagonals of period 2^k are R_0..R_J with k ≤ J ≤ 2^{k+1} − 2, and rows 2^k u (u odd), 2^k − 1 have the stated ends.'),
    ('zero_gap_cell', 'Row 2^k u (u odd) reads 1 0^J 1 leftwards from its right edge.'),
    ('last_one', 'The last cell of every period is black.'),
    ('last_white', 'R_{J+1}(2^k − 1) = 0 for the last diagonal J of period 2^k.'),
    ('restart', 'R_j reads the same at times 2^k u + s and s.'),
    ('row_restart', 'Row 2^k + s ends with a copy of row s.'),
    ('center_restart', 'Column 2^k u repeats c(0), …, c(J) below the right edge.'),
    ('column_continuity', 'Columns p and p + 2^k u agree s steps after the edge reaches them (when R_s has period 2^k).'),
    ('center_black_lt', 'A black c(t) lies in the first period of diagonal t: t < 2^k.'),
    ('exists_IsE', 'e_j exists for every j.')]:
    add(s, 'rp_' + nm, 'RP', nm, 'kernel' if nm in ('per_14', 'per_23') else 'thm', txt)
# ---------------------------------------------------------------- 5.1
s = 's5-q01'
add(s, 'bar_stripe_fixed', 'BAR', 'stripe_fixed', 'thm', 'The stripe is a fixed point (barrier encoding z).')
add(s, 'trunc_survives', 'BAR', 'trunc_survives', 'thm', 'The truncated stripe trunc n (n odd) keeps depth 1 black at every t ≤ n and white at n+1.')
add(s, 'lasso', 'BAR', 'finite_abstraction_has_lasso', 'thm', 'B1: any abstraction into bit-lists of length w repeats a value along one surviving truncated-stripe run.')
add(s, 'z_width', 'BAR', 'z_width', 'thm', 'The edge of a finite ZBL row moves out one depth per step.')
add(s, 'z_shift', 'BAR', 'z_shift', 'thm', 'Translation invariance away from the wall.')
add(s, 'no_local_ranking', 'BAR', 'no_local_ranking', 'thm', 'B2: no R(width, wall window, edge window) ∈ ℕ strictly decreases along every surviving double step of every finite start.')
add(s, 'lasso_gen', 'COR', 'finite_abstraction_has_lasso_gen', 'thm', 'B1 for abstractions into any finite set.')
add(s, 'reachable_cycle', 'COR', 'sound_abstraction_has_reachable_cycle', 'thm', 'Every sound finite abstract transition relation has a cycle reachable from a finite start.')
add(s, 'no_finite_abstract_ranking', 'COR', 'no_finite_abstract_ranking', 'thm', 'No ranking through a finite abstraction decreases along all surviving double steps.')
add(s, 'prose_off_by_one', 'COR', 'prose_off_by_one', 'thm', 'Sanity check: the round-2 prose bound j ≤ 2^w + 1 was off by one (the proof needs only j ≤ 2^w).')
add(s, 'no_edge_dfa', 'DFA', 'no_edge_dfa_ranking', 'thm', 'B6: no DFA (any number of states) reading a finite row from its edge defines a ranking (longest accepted prefix).')
# ---------------------------------------------------------------- 5.2
s = 's5-joint'
add(s, 'no_joint_local_ranking', 'JB', 'no_joint_local_ranking', 'thm', 'No R(lo, hi, center window, left-edge window, right-edge window) ∈ ℕ decreases at every step where the center flips, over all finite configurations.')
# ---------------------------------------------------------------- 5.3
s = 's5-edge'
add(s, 'complete_near_wall', 'CORE', 'complete_near_wall', 'thm', 'Any far part can be completed near the wall so that column -1 follows any prescribed values up to time d-1.')
add(s, 'far_light_cone', 'CORE', 'far_light_cone', 'thm', 'Rows agreeing from depth d agree from depth d+t at time t.')
add(s, 'edge_region_barrier', 'CORE', 'edge_region_barrier', 'thm', 'Edge-region barrier: for every far part z and every prescription c of column -1 there is a row equal to z beyond depth d, with the same edge region at all times, whose column -1 follows c up to time d-1.')
add(s, 'barrier_exists', 'DL', 'barrier_exists', 'thm', 'For every driver, n ≥ 1 and target b, some start with leftmost black cell at -n has column -1 = b at steps 0..n-2.')
add(s, 'barrier_unique', 'DL', 'barrier_unique', 'thm', 'That start is unique.')
add(s, 'rz_realize', 'RZ', 'realize', 'thm', 'For any right half R and target column c, `conf R c` has right half R and column 0 equal to c.')
add(s, 'rz_unique', 'RZ', 'unique', 'thm', 'A configuration is determined by its right half and its column 0.')
add(s, 'column_realizable_unique', 'RZ', 'column_realizable_unique', 'thm', 'Every column is realizable with any right half, uniquely.')
add(s, 'seed_perturbation', 'RZ', 'seed_perturbation', 'thm', 'For every n, a configuration equal to the seed on p ≥ -n has center c(t) for t ≤ n and white after.')
add(s, 'run_not_adjacent', 'RZ', 'run_not_adjacent', 'thm', 'Jen’s adjacent-column theorem for every rule left ⊕ g(center, right) with g(0,0) = 0, g(0,1) = 1.')
add(s, 'run30_eq_cell', 'RZ', 'run30_eq_cell', 'thm', 'The general run with g = or is rule 30.')
add(s, 'center90', 'RZ', 'center90', 'thm', 'Rule 90 single-seed center: 1, 0, 0, …')
add(s, 'center150', 'RZ', 'center150', 'thm', 'Rule 150 single-seed center: constantly 1.')
add(s, 'center210', 'RZ', 'center210', 'thm', 'Rule 210 single-seed center: 1, 0, 0, …')
add(s, 'rz_barrier', 'RZ', 'barrier', 'thm', 'Rules 90, 150, 210 satisfy generalized Jen and yet have eventually periodic centers.')
# ---------------------------------------------------------------- 7
s = 's7'
add(s, 'never_S0001', 'EW', 'never_enters_S0001', 'thm', 'An explicit finite right half (ether columns 1..17, wall state on 18..30) driven by (0001)^∞ never enters the round-1 trap S0001.')
add(s, 'never_S0011', 'EW', 'never_enters_S0011', 'thm', 'The same for 0011 and S0011.')
add(s, 'never_S0111', 'EW', 'never_enters_S0111', 'thm', 'The same for 0111 and S0111.')
