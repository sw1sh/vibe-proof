# -*- coding: utf-8 -*-
"""Prose of rule30-state.html.  Placeholders:
  [[T:key]]  link to theorem row (shows its id)        [[N:key]] link showing the Lean name
  [[C:id]]   link to computation row                    {{chip:kind}} status chip
"""

ABSTRACT = """Problem 1 of the Rule 30 Prize asks whether the center column c of rule 30 started from a
single black cell is never eventually periodic; it remains open after two rounds. What is proved in Lean 4
(every cited theorem's axioms re-printed in this pass; only propext, Classical.choice and Quot.sound occur)
is a ring of unconditional partial results: Jen's theorem, no eventually constant column, masked and
effective-boundary forms of Jen, the periods of the diagonals, the nine-black shield with Theorems B, B′
and D, three individually certified repeating words plus a table of thirty and several infinite word
families, the kernel-checked bound T + P ≥ 16359 on any eventual period P with transient T, and the
statement that the black-seed and white-seed centers are not both eventually periodic. Eventual period 2
is reduced to Q01, a statement about the zero-boundary left half (ZBL) that is proved equivalent to three
other forms (LR, bounded white runs, and “Φ(f) is never finitely supported”), and to a weaker coupled
condition CQ01 that also uses the right half; least period 4 is reduced to the Lean propositions Absorption(w)
and C3(w), the second built on Lean skeleton theorems for the right half. The constrained ZBL is proved conjugate to the full shift on its free bits, its histories split into
epochs, and stripe tails are absorbed. Barrier theorems in Lean show that finite abstractions, local
rankings and edge automata cannot prove Q01 (their truncated-stripe witnesses violate the right-half
constraint), that two-sided local rankings fail on truncations of the period-4 ether, and that windows
near the edge carry no information; computation finds no additive conservation law of small range.
Computations, cross-validated where stated, support the open hypotheses: every ZBL start of width W ≤ 71 dies by time
2W + 8, every finite right half tested enters the ether-and-wall family, and the right half driven by an
alternating center emits column-1 values in blocks 100 and 10000 with density 3/14. The round-1
single-trap claim, low-complexity certificates and simple monovariants are refuted. The gap is now
sharply located: a global argument that a finitely supported configuration cannot sustain the coupled
period-2 (or period-4) constraints forever."""

GLANCE = """
<div class="glance">
  <div class="g-item"><span class="chip open">open</span><p><b>Problem 1.</b> No eventual period P ≥ 2 is excluded
  for all repeating words of that period. Period 1 is excluded ([[N:no_column_const]]).</p></div>
  <div class="g-item"><span class="chip ok">proved</span><p><b>Unconditional.</b> T + P ≥ 16359 ([[N:transient_add_period_ge]]);
  32 certified words, the families 0 1<sup>k</sup> (k ≥ 9), 0<sup>r</sup>11 (r ≥ 10), 1<sup>r</sup>u (Theorem B′), and every
  period with a long black run (Theorems B, D).</p></div>
  <div class="g-item"><span class="chip impl">implication</span><p><b>Period 2</b> ⟸ CQ01 ⟸ Q01 ⟺ LR ⟺ BWR ⟺ “Φ(f) never
  finite”. <b>Least period 4</b> ⟸ Absorption(w), and ⟸ C3(w). All hypotheses open.</p></div>
  <div class="g-item"><span class="chip ok">proved</span><p><b>Barriers.</b> Finite abstractions, local and edge-DFA
  rankings cannot prove Q01; two-sided local rankings cannot exclude period 2; short near-edge windows carry nothing.</p></div>
  <div class="g-item"><span class="chip comp">computed</span><p><b>Evidence.</b> D(W) ≤ 2W + 8 for W ≤ 71 (four codes);
  absorption in 282,144 runs per word; block law 100/10000 with density 3/14.</p></div>
  <div class="g-item"><span class="chip ref">refuted</span><p><b>Dead ends.</b> One fixed trap per word; low-complexity
  descriptions of the right half; 15 simple monovariants; additive conservation laws of range ≤ 8.</p></div>
</div>
"""

S1 = r"""
<section id="s1">
<h2><span class="secno">1</span> Problem 1, its Lean statement and the definitions</h2>

<h3 id="s1-stmt">1.1 The statement</h3>
<p>Rule 30 updates a cell from its left neighbour l, itself c and its right neighbour r as
l ⊕ (c ∨ r). Started from one black cell at position 0, the pattern is <code>cell t p</code>; the center
column is c(t) = <code>cell t 0</code> = 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, … (OEIS A051023).
Problem 1 asks that c never becomes periodic, whatever the transient. In Lean
(<code>ruliology-lean/Ruliology/CellularAutomata/Rule30Jen.lean</code> and <code>Rule30Prize.lean</code>):</p>
<div class="codeframe"><pre><code>def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def EventuallyPeriodic (f : Nat → Bool) : Prop :=
  ∃ T P : Nat, 0 &lt; P ∧ ∀ t, T ≤ t → f (t + P) = f t

def center (t : Nat) : Bool := cell t 0

/-- Problem 1: the center column is not eventually periodic. -/
def Problem1 : Prop := ¬ EventuallyPeriodic center   -- Rule30Prize.Problem1</code></pre></div>
<p>The module docstring states that this matches <code>Rule30.centerColumn_not_eventually_periodic</code> in
google-deepmind/formal-conjectures; that correspondence was not re-checked in this pass. Problem 1 is open.
[[N:problem1_iff_no_word]] restates it as the exclusion of every nonempty repeating word: c = w<sup>∞</sup>
from some time on (<code>EventuallyWord w</code>) is impossible for every w ≠ [] . Each word exclusion below is
therefore one piece of Problem 1, valid for every transient and every phase.</p>

<h3 id="s1-defs">1.2 Objects used throughout</h3>
<div class="tframe"><table class="deftab">
<thead><tr><th>Object</th><th>Definition</th><th>Lean</th></tr></thead>
<tbody>
<tr><td>Diagonals</td><td>R<sub>j</sub>(t) = cell t (t − j) from the right edge, D<sub>j</sub>(t) = cell t (j − t) from the left edge; c(t) = R<sub>t</sub>(t) = D<sub>t</sub>(t).</td><td><code>Rule30Diagonals.R</code>, <code>.D</code></td></tr>
<tr><td>orCol</td><td>orCol i (t) = cell t i ∨ cell t (i+1); column i−1 is rebuilt from column i and orCol i.</td><td><code>Rule30MaskedJen.orCol</code></td></tr>
<tr><td>Effective boundary</td><td>c′(t) = c(t) ∧ c(t+1). The left half sees the center only through c′ ([[N:effective_boundary]]).</td><td><code>Rule30MaskedJen.effective_step</code></td></tr>
<tr><td>Driven halves</td><td>L c s: rule 30 on p &lt; 0 with column 0 prescribed as c, started from s. drv c x: rule 30 on p ≥ 1 with column 0 prescribed.</td><td><code>Rule30DrivenLeft.L</code>, <code>R30EtherWall.drv</code></td></tr>
<tr><td>ZBL</td><td>Zero-boundary left half: L with c ≡ 0. If c alternates, c′ ≡ 0 and the real left half is a ZBL orbit ([[N:left_half_zero_driven]]).</td><td>three encodings, below</td></tr>
<tr><td>Constraint, free bits</td><td>Period 2, phase 0: column −1 black at every even step. Free bits f<sub>s</sub> = column −1 at step 2s+1.</td><td><code>R30ProgA.alt f</code></td></tr>
<tr><td>Forced row Φ(f)</td><td>The unique ZBL row whose column −1 is 1, f<sub>0</sub>, 1, f<sub>1</sub>, … (sideways reconstruction). Also written lam (alt f) and Θ(f).</td><td><code>R30ZBL.Phi</code>, <code>R30ProgA.lam</code>, <code>A1ReformCheck.Theta</code></td></tr>
<tr><td>Stripe</td><td>…10101 (black at odd depths): a ZBL fixed point that satisfies the constraint forever, with f = 1<sup>∞</sup>.</td><td><code>Rule30PeriodTwo.stripe</code></td></tr>
<tr><td>Ether</td><td>The spatial-period-7, temporal-period-4 rule-30 orbit with columns B1…B5, c, c = 0011, 0110, 1101, 0101, 0011, 0001, 0001 (phases 0–3).</td><td><code>R30EtherWall.ether</code></td></tr>
<tr><td>W109 wall</td><td>109 states (phase, 13-cell strip) to the right of a B3 ether column, closed under every input from the right.</td><td><code>R30EtherWall.wallStates</code></td></tr>
<tr><td>Strip relaxation</td><td>Columns 1..b updated exactly, column b+1 arbitrary at every step. Every true right half is a path in it.</td><td><code>Rule30StripCertificates</code></td></tr>
<tr><td>D(W)</td><td>The largest first-violation time (first even step with column −1 white) over ZBL rows supported on depths 1..W.</td><td>computed, §6.1</td></tr>
</tbody></table></div>

<p>Three encodings of the ZBL appear in the round-2 files. They describe the same system and their Q01 statements
are the same mathematical statement. In the round-2 files only the bridge from <code>R30ProgA.Q01</code> to the
staged <code>Rule30PeriodTwo.Q01</code> is formalized ([[N:Q01_iff_staged]]). The integration task has since merged
the three into one staged module, <code>Rule30ZeroBoundary</code>, in the zrow encoding, whose Q01 is proved to be the
staged one ([[N:zb_Q01_iff_staged]]). This report cites the round-2 originals together with the new glue theorems
of the staged modules (§C).</p>
<div class="tframe"><table class="deftab">
<thead><tr><th>Namespace (file)</th><th>Index convention</th><th>Q01</th></tr></thead>
<tbody>
<tr><td><code>R30ProgA</code> (progA-backdet/lean/ZBLCore.lean)</td><td><code>zorb x t i</code>: index i is position −(i+1); the wall is implicit.</td><td>∀ x finite, ¬ ∀ s, zorb x (2s) 0 = 1</td></tr>
<tr><td><code>ZBL</code> (A-monovariant/lean/ZBL.lean)</td><td><code>run x t k</code>: depth k ≥ 1 is position −k; x 0 is the white wall.</td><td>stated as <code>q01_width_le_16</code> for width ≤ 16</td></tr>
<tr><td><code>R30ZBL</code> (A-reconmap/lean/ZBL.lean)</td><td><code>zrow L t k</code>: depth k, k = 0 the wall.</td><td>∀ L, FinSupp L → ¬ InX L</td></tr>
</tbody></table></div>
</section>
"""

S2 = r"""
<section id="s2">
<h2><span class="secno">2</span> Unconditional results about the single-seed pattern</h2>
<p class="lead">Everything in this section is {{chip:ok}} in Lean and holds for every transient. File paths and
axiom lists are in the <a href="#theorems">theorem index</a>.</p>

<h3 id="s2-jen">2.1 Jen’s theorem and constant columns</h3>
<p>Rule 30 is left-permutive ([[N:cell_left]]), so two adjacent columns that are periodic from a common time
force every column to their left to be periodic ([[T:periodic_left_all]]), which the left edge forbids
([[T:left_edge]], [[T:no_left_periodic]]). Between two non-adjacent periodic columns the strip is finite-state,
and pigeonhole makes the next column periodic ([[T:between_periodic]]). Hence [[N:jen]] (Jen 1986): two different
columns are never both eventually periodic, and at most one column is ([[T:periodic_column_unique]]).</p>
<p>[[N:no_column_const]]: no column is eventually constant. An eventually black column makes its left neighbour
eventually white; an eventually white column makes its right neighbour monotone, hence eventually constant; both
contradict Jen. This is Problem 1 for period 1 ([[T:center_not_p1]]).</p>

<h3 id="s2-diag">2.2 Diagonal periods</h3>
<p>The diagonals obey R<sub>j+2</sub>(t+1) = R<sub>j+2</sub>(t) ⊕ (R<sub>j+1</sub>(t) ∨ R<sub>j</sub>(t)) and
D<sub>j+2</sub>(t+1) = D<sub>j</sub>(t) ⊕ (D<sub>j+1</sub>(t) ∨ D<sub>j+2</sub>(t)) ([[T:R_step]], [[T:D_step]]).
Every right diagonal is periodic from time 0 with period 2<sup>j</sup> ([[N:R_periodic]]) and every left diagonal is
eventually periodic with period 2<sup>j</sup> ([[N:D_periodic]]). The center is the diagonal of diagonals,
c(t) = R<sub>t</sub>(t) = D<sub>t</sub>(t), and for t ≥ 2 it is a parity:
c(t) = #{s &lt; t : cell s (s−t+1) ∨ cell s (s−t+2)} mod 2 ([[T:center_eq_parity]]). Since 2<sup>j</sup> &gt; j these
facts say nothing about c directly; the finer right-diagonal theory is in §4.9.</p>

<h3 id="s2-win">2.3 Kernel-checked windows</h3>
<p>The first 16384 center bits are computed inside the Lean kernel on packed rows ([[T:row_testBit]],
[[T:center_eq_bit]]). Two consequences:</p>
<ul>
<li>[[N:no_small_eventual_period]]: no eventual period P ≤ 4096 with transient T ≤ 8192.</li>
<li>[[N:transient_add_period_ge]]: if c(t+P) = c(t) for all t ≥ T and P &gt; 0, then <b>T + P ≥ 16359</b>. The 16359
factors of length 26 starting at 0, …, 16358 are pairwise distinct ([[T:win_inj]], a kernel-checked sorted
certificate), and an eventual period would repeat the factor at T at T + P.</li>
</ul>
<p>Round 1 also recorded T + P ≥ 9,999,957, conditional on the external center-column data. That bound depends on
data outside Lean and is {{chip:comp}} only.</p>

<h3 id="s2-mj">2.4 Masked Jen and the effective boundary</h3>
<p>Column i+1 enters the reconstruction of column i−1 only through orCol i, that is, only at the white times of
column i ([[T:left_of_black]], [[T:left_of_white]]). Hence [[N:masked_jen]]: if column i has period P from T,
column i+1 is not P-periodic from T on the white times of column i. Equivalent forms:
[[T:masked_jen_center]], [[T:center_masked]], [[T:orCol]]. The same observation gives the effective boundary
[[N:effective_boundary]]: cell t (−1) ∨ c(t) = cell t (−1) ∨ (c(t) ∧ c(t+1)), so column −1 evolves with
c(t) ∧ c(t+1) in place of c(t) ([[T:effective_step]]). Without any periodicity assumption, two times
t₁ &lt; t₂ never carry the same (center, orCol 0) window of length t₂ ([[T:window_jen]], [[T:window_jen_col]]);
under period P from T every doubling interval [n, 2n) with n ≥ T+P contains a white center time where column 1
breaks period P ([[T:periodic_window]]); and a finitary version holds on [n−P, 2n] ([[T:finitary_jen]]).
Masked Jen is the contradiction used by every right-half argument in this report.</p>

<h3 id="s2-br">2.5 The nine-black shield and black runs</h3>
<p>[[N:nine_black]] (Lemma A): if column m is black at times t, …, t+8, then at time t+9 column m+1 is white and
column m+2 black, whatever lies to the right. The proof is a kernel check over the 2<sup>11</sup> contents of
columns m+1..m+11 ([[T:nine_black_core]]); eight steps do not suffice ([[T:eight_black_not_enough]]).
Iterating, a black run of length 9j forces (white black)<sup>j</sup> in the next 2j columns ([[N:black_shield]]).
Consequences, all for every transient:</p>
<ul>
<li>A column whose black runs followed by white all have length ≥ 9 is not eventually periodic
([[T:long_runs_col]], [[T:long_runs]], finitary form [[T:finitary_long_runs]]). In particular
c ≠ (0 1<sup>k</sup>)<sup>∞</sup> eventually for k ≥ 9 ([[T:zero_ones]]).</li>
<li>Theorem B ([[N:thmB]]): a period of length P cannot contain a black run of length r with
9⌈(P−r+9)/2⌉ ≤ r (roughly r ≥ 0.82P + 8.2).</li>
<li>Theorem B′ ([[N:thmBprime]]): if the finite check <code>Determined u j0</code> holds, c is never eventually
(1<sup>r</sup>u)<sup>∞</sup> with r ≥ max(9, 9j0). Kernel instances exclude u ∈ {0, 00, 000, 0000, 0100} for
r ≥ 18 and u ∈ {010, 0010, 0110} for r ≥ 27 ([[T:det_0]]–[[T:det_0110]]); for example (1<sup>r</sup>0)<sup>∞</sup>,
r ≥ 18 ([[T:black_run_then_white]]).</li>
<li>Theorem D ([[N:thmD]]): a period cannot contain a black run s ≥ 9 immediately followed by a white run
r ≥ 1 + 9⌈(k+8)/2⌉, where k = P − s − r.</li>
<li>(0<sup>r</sup>11)<sup>∞</sup> is excluded for r ≥ 10 ([[N:white_run_11]]).</li>
</ul>

<h3 id="s2-sc">2.6 Strip-certificate word exclusions</h3>
<p>If c = w<sup>∞</sup>, the cells right of the center evolve in the strip relaxation. A finite certificate showing
that column 1 is eventually periodic at the white phases of w then contradicts masked Jen. Two certificate
kinds are proved sound: bitmask certificates ([[N:word_strip]]) and rank certificates, whose counter returns
after m·|w| steps ([[T:iterG_period]]) and whose soundness is [[N:Cert_sound]]. Kernel-checked instances:</p>
<ul>
<li>0 1<sup>7</sup> ([[T:w01111111]], bitmask, width 5); 0<sup>6</sup>11 ([[T:w00000011]], rank, width 6, 379 ranks);
0<sup>9</sup>101 ([[T:w000000000101]], rank, width 7, 1309 ranks).</li>
<li>Thirty words of lengths 8–13 ([[T:certTable_ok]], [[N:certTable]]), each written as its least rotation:
<span class="wordlist">01111111; 0000000011, 0011111111, 0111111111; 00000000001, 00000000011, 00111111111,
01011111111, 01111111111; 000000000001, 000000000011, 000111111111, 001111111111, 010111111111, 011111111111;
0000000000001, 0000000000011, 0000000000101, 0000000001011, 0000000010011, 0000000101111, 0000111111111,
0001011111111, 0001111111111, 0010111111111, 0011111111101, 0011111111111, 0101111111111, 0110111111111,
0111111111111</span>. Only the certificates are checked, not the completeness of the search that found them.</li>
</ul>

<h3 id="s2-ws">2.7 White seed and rule 135</h3>
<p>Rule 30 from one white cell on black becomes, after one step, the usual pattern shifted by one cell
([[T:cellW_succ]]); rule 135 from one black cell is the usual pattern shifted and complemented ([[T:cell135_succ]]).
With Jen applied to columns 0 and −1: the black-seed and white-seed centers of rule 30 are not both eventually
periodic ([[N:black_or_white]]), and likewise rules 30 and 135 ([[T:r30_or_135]]). Which one is aperiodic is left
open.</p>
</section>
"""

S3 = r"""
<section id="s3">
<h2><span class="secno">3</span> Reductions</h2>
<p class="lead">Each reduction is stated with its hypothesis. {{chip:impl}} marks a proved Lean theorem whose
hypothesis is open; {{chip:paper}} marks an argument assembled from Lean lemmas but not itself formalized.</p>

<h3 id="s3-p2">3.1 Period 2 ⟸ Q01 ⟺ LR ⟺ BWR ⟺ “Φ(f) never finitely supported”</h3>
<p><b>What a period 2 would force.</b> If c(t+2) = c(t) for t ≥ T₀ then, since c is not eventually constant, c
alternates from some T, black at T+2k ([[N:normalize]]). Then column −1 is black at every black step
([[T:m1_even]]); at the white steps column 1 is the complement of column −1 ([[T:p1_odd]], [[T:left_right_white]]);
the free bits f<sub>k</sub> = cell (T+2k+1) (−1) never contain 00 ([[N:golden]]); column −4 is white at every white
step ([[T:m4_odd]]); where the center reads 0101 on [t, t+3], column 1 never reads 0000 or 0101 there, and
where it reads 01010101 it never reads 00010001 ([[T:no_AA]], [[T:no_BB]], [[T:no_ABAB]]). The effective boundary is white ([[T:effective_white]]), so the left half from T on is the
zero-boundary left half started from the finite row at T ([[N:left_half_zero_driven]]; second and third proofs
[[T:left_half_is_zbl]], [[T:cell_eq_zrow]]).</p>

<div class="stmt"><div class="stmt-h">Q01 <span class="chip open">open</span></div>
<p>No finitely supported row of the zero-boundary left half keeps column −1 black at every even step.</p>
<pre><code>def Q01 : Prop :=                                   -- Rule30PeriodTwo.Q01
  ∀ (m : Nat) (s : Int → Bool), 0 &lt; m → (∀ p : Int, p &lt; -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, L (fun _ => false) s (2 * k) (-1) = true</code></pre></div>

<p>{{chip:impl}} <b>Q01 ⇒ c is not eventually 2-periodic</b>, for every transient: [[N:p2_of_Q01]], with
independent proofs in the other two encodings, [[T:no_eventual_period_two]] and [[T:no_period_two_of_Q01]].</p>
<p>{{chip:ok}} <b>Equivalent forms of Q01.</b></p>
<ul>
<li>LR: for every free-bit sequence f the forced row lam (alt f) is infinite ([[N:Q01_iff_LR]]).</li>
<li>BWR, bounded white runs: for every depth d there is B such that for every f the forced row has a black cell
in [d, d+B) ([[N:Q01_iff_bounded]], through compactness, [[T:uniform_death]]). As its docstring notes, the
optimal B is the largest survival time over supports ≤ d, minus d, plus one, which links BWR to D(W) of §6.1.</li>
<li>Φ(f) is never finitely supported ([[N:Q01_iff_Phi]], zrow encoding).</li>
<li>The general reading (either phase, constraint from any start time) is equivalent to “Θ(f) is never finite”
([[T:part_c1]]); compactness ([[T:koenig]], [[T:FW_closed]]) makes each width a finite search.</li>
<li>Q01 also gives the phase-1 version ([[T:Q01_phase1]]), and <code>R30ProgA.Q01</code> is the staged statement
([[T:Q01_iff_staged]]). In the unified staged encoding: [[T:zb_Q01_iff_Theta]], [[T:zb_Q01_any_phase]],
[[T:zb_Q01_iff_staged]].</li>
</ul>
<p><b>Finiteness is essential.</b> The infinite stripe satisfies the constraint forever ([[T:stripe_fixed_p2]],
[[N:stripe_col]]), and so does the left half of the ether, whose free bits alternate ([[T:ether_free_bits]]); the
ether even satisfies every coupled condition below except finite support ([[N:ether_coupled_witness]]).</p>

<div class="stmt"><div class="stmt-h">The coupled variant CQ01 <span class="chip open">open</span></div>
<p>Fix column 0 to alternate, black at even steps. CQ01 says there is no pair (L, R) of a finitely supported
ZBL row L and a finitely supported right half R such that (i) R evolves as the right half driven by the
alternating column (<code>R30EtherWall.drv</code>); (ii) column −1 of L is black at every black step; and
(iii) at every white step, column −1 of L is the complement of column 1 of R.</p></div>
<p>{{chip:impl}} <b>Q01 ⇒ CQ01 ⇒ no eventual period 2</b>, for every transient: [[N:CQ01_of_Q01]] and
[[N:p2_of_CQ01]], in the staged module <code>Rule30PeriodTwoCoupled</code> (compiled and checked in this pass). The
first arrow holds because a counterexample to CQ01 is, after forgetting R, a counterexample to Q01. For the second,
normalize ([[T:normalize]]) to alternation from T; the row at T on p ≤ −1 is finite with its edge at −T
([[T:left_white]], [[T:left_edge]]) and evolves as the ZBL ([[T:left_half_zero_driven]]); the row at T on p ≥ 1 is
finite by the right edge and evolves as the driven right half ([[T:cell_eq_drv]]); (ii) is [[T:m1_even]] and
(iii) is [[T:p1_odd]].</p>
<p><b>Right-half laws available to CQ01.</b> Under alternation the right half alone already constrains f:</p>
<ul>
<li>{{chip:ok}} f has no 00 ([[T:golden]]).</li>
<li>{{chip:ok}} f has no 11111: column 1 is black at some white step among any five consecutive white steps
([[N:col1_black_among_five]], a kernel check over the light cone of columns 1..11; with golden,
[[T:no00_no11111]]). Two independent programs agree that a width-4 strip relaxation already forces it while widths
1–3 do not ([[C:C5]]).</li>
<li>{{chip:comp}} Observed but unproved: after a transient, the output of every finite right half tested is a
concatenation of 100 and 10000, so f would be a concatenation of 011 and 01111 ([[C:C4]], §6.4).</li>
</ul>
<p>With the epoch theorem [[N:after_reset]] (§4.3), the runs of 1s in f are the lengths d/2 − 1 of the
successive epochs, so golden and no-11111 together say every epoch depth d lies in {4, 6, 8, 10}, and the block
law would leave {6, 10}. The truncated stripes that witness the Q01-only barriers of §5.1 have f = 1 for about
n/2 consecutive white steps and therefore violate no-11111.</p>

<h3 id="s3-p4">3.2 Least period 4 ⟸ Absorption(w)</h3>
<p>A word of length 4 with least period 4 is a rotation of 0001, 0011 or 0111; a rotation from time T is the word
itself from a later time, so it suffices to exclude c = w<sup>∞</sup> for these three words. Each of them is a
column of the ether up to a time shift (§4.6). The ether-and-wall family for an alignment (j0, s) consists of the
rows whose columns 1..k carry the ether (column k a B3, k ≡ 2 − j0 mod 7) and whose columns k+1..k+13 form one of
the 109 wall states.</p>
<div class="stmt"><div class="stmt-h">Absorption(w, A) <span class="chip open">open</span></div>
<pre><code>def InFamily (F : Nat → Nat → Bool) (j0 s t1 : Nat) : Prop :=
  ∃ k, (j0 + k) % 7 = 2 ∧ (∀ p, 1 ≤ p → p ≤ k → F t1 p = ether (j0 + p) (t1 + s)) ∧
    ((t1 + s) % 4, rowOf F t1 k 13) ∈ wallStates

def Absorption (w : List Bool) (A : List (Nat × Nat)) : Prop :=
  ∀ (x : Nat → Bool) (n : Nat), (∀ p, n &lt; p → x p = false) → ∀ φ : Nat,
    ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1</code></pre>
<p>Every finitely supported right half driven by w<sup>∞</sup>, in every phase, eventually enters the family for one
of the listed alignments (A0001 = [(5,0), (6,0)], A0011 = [(0,0), (1,3), (4,0)], A0111 = [(2,2)]).</p></div>
<p>{{chip:impl}} [[N:lp4_absorption]]: Absorption for 0001, 0011 and 0111 implies that c is not eventually
any rotation of these words, for every transient, i.e. c has no least period 4. The single-word form is
[[T:absorption_excludes]]. Inside the family the trap theorem [[T:ether_wall_trap]] applies: the ether columns
then stay periodic forever, so column 1 at the white times is periodic, against masked Jen. The hypothesis
quantifies over all finite right halves because a proof cannot know the true one. Evidence: §6.3 ([[C:C3]]).</p>

<h3 id="s3-c3">3.3 Least period 4 ⟸ C3(w), a paper reduction from Lean skeletons, now formalized</h3>
<p>The skeleton theorems (§4.7) say that if c = w<sup>∞</sup> from T (phase (t−T) mod 4), column −1 is eventually fixed
at three of the four phases. The effective boundary c′<sub>w</sub>(φ) = w(φ) ∧ w(φ+1) is 4-periodic:</p>
<div class="tframe"><table class="deftab narrow">
<thead><tr><th>w</th><th>c′<sub>w</sub></th><th>P<sub>w</sub> = column −1 at phases 0, 1, 2, 3</th><th>source</th></tr></thead>
<tbody>
<tr><td>0001</td><td>0000</td><td>0, *, 0, 1</td><td>[[N:skeleton_0001_explicit]] (eventually)</td></tr>
<tr><td>0011</td><td>0010</td><td>*, 0, 0, 1</td><td>[[N:skeleton_0011_explicit]] (eventually)</td></tr>
<tr><td>0111</td><td>0110</td><td>*, 0, 0, 1</td><td>[[N:column_m1_0111]] (for all t ≥ T)</td></tr>
</tbody></table></div>
<div class="stmt"><div class="stmt-h">C3(w) <span class="chip open">open</span></div>
<p>No finitely supported left configuration, evolving by rule 30 on p ≤ −1 with column 0 replaced by the
4-periodic boundary c′<sub>w</sub>, keeps column −1 equal to P<sub>w</sub> at the three fixed phases for all
large t.</p>
<pre><code>def C3 (w : List Bool) : Prop :=                 -- Rule30PeriodFourSkeleton.C3
  ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p &lt; -(M : Int) → s p = false) →
    ¬ ∃ K, ∀ k, K ≤ k →
      fits (colPattern w) (k % 4) (Rule30DrivenLeft.L (fun k => wordAt (effWord w) k) s k (-1)) = true</code></pre></div>
<p>{{chip:impl}} <b>C3(w) ⇒ c is never eventually w<sup>∞</sup></b>, for every transient: [[N:n0001_of_C3]],
[[N:n0011_of_C3]], [[N:n0111_of_C3]], combined in [[N:lp4_C3]] (staged module <code>Rule30PeriodFourSkeleton</code>,
compiled and checked in this pass). The argument is the round-2 paper reduction: suppose c = w<sup>∞</sup> from T. The
skeleton theorem gives T′ ≥ T after which column −1 matches P<sub>w</sub>; pick T″ ≥ T′ with T″ ≡ T mod 4. By
[[N:dl_cell_eq_L_eff]] the left half from T″ is the half driven by c(T″+k) ∧ c(T″+k+1) = c′<sub>w</sub>(k mod 4)
from the row at T″, which is finite with its edge at −T″ ([[T:left_white]], [[T:left_edge]]), and that row
violates C3(w) ([[T:not_tail_of_C3]]). The phase conventions in the table were checked against the three skeleton
statements and agree with the Lean definitions <code>effWord</code> and <code>colPattern</code>.</p>
<p>C3(w) is not trivially false: for each w, neither the empty start nor any start with its leftmost black cell
at depth ≤ 14 keeps the pattern P<sub>w</sub> on the window [150, 300) ({{chip:comp}} [[C:C13]]).</p>
<p>For w = 0001 the boundary c′ is identically white, so C3(0001) is a question about the same ZBL as Q01,
with the period-4 pattern 0, *, 0, 1 in place of the period-2 constraint. The right half again restricts the
free phase: the free bits of 0001 never contain 11 eventually ([[N:no11_0001]]).</p>
</section>
"""

S4 = r"""
<section id="s4">
<h2><span class="secno">4</span> Structural theorems about the auxiliary systems</h2>
<p class="lead">All {{chip:ok}} in Lean. Most concern the ZBL under the period-2 constraint; §4.6–4.7 concern the right
half under period 4; §4.8–4.9 are round-1 results on the driven left half and the right diagonals.</p>

<h3 id="s4-real">4.1 ZBL realization and conjugacy to the full shift</h3>
<p><b>Realization.</b> Column −1 determines the row: for every sequence a there is exactly one ZBL row whose column
−1 is a, namely lam a ([[N:realization]]; also [[T:zrow_det]], [[T:trace_surj]]). The dependence is triangular:
row cell k+1 is the k-th column value plus a function of the earlier ones ([[T:zrow_pivot]], [[T:pivot]]). For
constrained rows: Φ(f)(2s+2) = f<sub>s</sub> ⊕ g<sub>s</sub>(f<sub>0..s−1</sub>), Φ(f)(2s+3) depends only on
f<sub>0..s</sub>, and flipping f<sub>s</sub> flips Φ(f)(2s+2) ([[T:V_d_even]], [[T:V_d_odd]], [[T:V_d_pivot_flip]];
also [[T:tri_even_form]], [[T:tri_odd_form]]). The first cells are L2 = ¬f₀, L3 = f₀, L4 = ¬f₁, L5 = f₀
([[T:small_identities]]). A row is constrained iff it is Θ(f) for some f ([[N:part_a]], [[T:V_Phi_unique]]).</p>
<p><b>Conjugacy.</b> Two ZBL steps of the forced row of f give the forced row of the shifted sequence:
Z² ∘ Φ = Φ ∘ σ ([[N:two_step_shift]], [[T:V_F2_Phi]], [[T:equivariance]]). Θ is injective with a continuous
inverse on its closed image ([[T:Theta_inj]], [[T:inverse_dep]], [[T:S_closed]]), and each coordinate of Θ(f)
depends on finitely many f<sub>s</sub>. So the constrained two-step ZBL is topologically conjugate to the
one-sided full 2-shift on the free bits, and Q01 asks whether this conjugacy ever reaches a finitely supported row.
Counting: exactly 2<sup>⌊W/2⌋</sup> of the 2<sup>W</sup> rows of width ≤ W satisfy the constraint at every even
t ≤ W − 1 ([[N:part_d]]), so before time W each even step halves the count, as the triangular structure predicts.</p>
<p><b>Determinism and locality.</b> Backward determinism at forced steps ([[T:backward_det]], [[T:history_det]]), a
finite-preimage criterion ([[T:back_fin_iff]]), light cones ([[T:core_light_cone]], [[T:col_light_cone]]),
zero-run localization ([[T:zero_run_local]]), and the one-step forced skeleton: at a forced black step the next one
is black iff cells 2 and 3 differ ([[T:survive_iff]], [[T:col2_doubling]], [[T:col3_of_col2]],
[[T:no_two_white]]).</p>

<h3 id="s4-clock">4.2 Jen with a clock</h3>
<p>[[N:jen_clock]]: if column −1 of a finite ZBL row with edge at depth m is P-periodic on [T, T+L], then
L + 2 ≤ T + m + 2P. Jen’s theorem is the limit L → ∞ ([[T:col_not_ep]]; other proofs [[T:col1_periodic_white]],
[[T:trace_not_ep]]). Under the constraint, a p-periodic stretch of free bits starting at s₀ has length ℓ with
2ℓ + 2 ≤ 2s₀ + m + 4p ([[T:free_bits_clock]]); the free bits of a finite constrained row are never eventually
periodic ([[T:constrained_col1_aperiodic]], [[T:free_not_ep]]) and never eventually 1 ([[T:col1_not_eventually_true]]).
For rule 30 itself, under alternation from T, column −1 and column 1 at the white times cannot be p-periodic on a
window [k₀, k₀+ℓ] with 2ℓ + 2 &gt; 2k₀ + T + 1 + 4p ([[N:alt_free_clock]], [[N:alt_right_clock]]). The second is the
interface for right-half arguments: a long periodic window of column 1 at white times would exclude period 2.</p>

<h3 id="s4-epoch">4.3 Epochs</h3>
<p>Compare a constrained history with the stripe. The first deviation from the stripe moves one cell toward the wall
per step and turns depth 1 white when it arrives ([[T:first_defect_run]], [[T:first_defect_hits]]); in a constrained
history it sits at an even depth at even times ([[T:first_defect_even]], [[T:first_defect_parity]]). With depth 1
black, a free bit is 0 exactly when the first deviation is at depth 2 ([[T:free_bit]], [[T:free_bit_iff]]), and at
such a reset the row is 0, 1, s₃, …, s<sub>d</sub> followed by a deviation at depth d+1 ([[T:reset_config]]). An
epoch that starts at an even time survives exactly when its depth d is even ([[N:epoch_survives_iff]],
[[T:epoch_col1]]). After a reset the free bits are 1 for d/2 − 1 white steps and then 0 ([[N:after_reset]]). So a
constrained history is a sequence of epochs, and f records their depths. For rule 30 under alternation the bridge
is phase-free: at every time u ≥ T+1 the first deviation depth is even exactly when c(u) = 1
([[N:alt_first_defect_phase]]; unified staged form [[T:first_defect_phase]]). The earlier one-phase statement [[T:alt_first_defect_parity]] is correct for its
phase, and [[T:alt_other_phase]] shows that its prose, read for the other phase, is false.</p>

<h3 id="s4-stripe">4.4 Stripe stability and absorption</h3>
<p>Stripe tails never recede over two steps ([[N:agrees_two_steps]]), and a preimage of a row that is the stripe
from depth L is the stripe from L + 4 ([[T:agrees_pre]], [[T:agrees_pre_run]]); so a finite row never becomes
stripe-tailed ([[T:finite_never_stripe]]). Conversely a row that agrees with the stripe from an odd position stays
so ([[T:stripe_confined]]), its front advances by two cells within 9 steps (kernel check over 2<sup>12</sup> contents,
[[T:front_check]], [[T:front_advance]]), and it becomes exactly the stripe ([[N:stripe_absorb]]); its free bits are
then eventually 1 ([[T:stripe_tail_one]]). The even-phase stripe behaves the same on depths ≥ 2 with depth 1
alternating, giving free bits eventually 0 ([[T:stripe2_absorb]], [[T:stripe2_tail_zero]]). Stripe backgrounds
absorb; the white background of a finite row is what lets the edge escape. Consequently Θ(f) is eventually the
stripe iff f is eventually 1 ([[N:Theta_eventually_stripe_iff]], staged; it combines [[T:two_step_shift]],
[[T:agrees_pre_run]] and [[T:stripe_tail_one]], and settles conjecture A8 of the round-2 monovariant study).</p>

<h3 id="s4-small">4.5 Kernel width checks</h3>
<p>[[N:q01_width_le_16]]: every row of width ≤ 16 has column −1 white at some even time &lt; 34 (packed exhaustive
search, [[T:check_16]]); the odd phase holds for width ≤ 15 ([[T:q01_width_le_15_odd]]). Transported to rule 30,
the center cannot alternate from any T ≤ 15 ([[T:not_alt_small]]), a consistency check far weaker than §2.3.</p>

<h3 id="s4-ether">4.6 The ether and the W109 wall</h3>
<figure class="fig ether-fig"><canvas id="etherCanvas" width="420" height="168" aria-label="Twelve steps of the ether: rule 30 on a ring of 7 cells with one black cell, three spatial periods shown, the B4 column highlighted"></canvas>
<figcaption>The ether: twelve steps of rule 30 on a 7-periodic row with one black cell per period (three periods
shown). The highlighted column (B4) alternates 0, 1, 0, 1, so the ether is a two-sided, spatially periodic
solution of the period-2 constraints.</figcaption></figure>
<p>The ether is a rule-30 orbit with temporal period 4 ([[T:ether_rule]], [[T:ether_period]]). The words 0001,
0011, 0111 and 0101 are ether columns up to a time shift ([[T:aligned_0001_5]]–[[T:aligned_0101_3]]). The wall is a
set of 109 states of a 13-cell strip next to a B3 column, closed under every value of the cell to its right and
carrying B4 next to a white B3 ([[N:wallOK_true]], a decide check; [[T:wall_facts]]). Ether on columns 1..k
followed by a wall state persists forever ([[N:trap_invariant]]); if c is an ether column, the true row can never
enter this family ([[T:ether_wall_trap]], [[T:no_ether_wall_entry]]), which is what Absorption exploits. The
configurations of [[T:config_pure_ether]] stay pure ether forever and avoid the round-1 traps (§7.1).</p>
<p>The period-7 row c7 (black at p ≡ 6 mod 7) returns after four steps and its column 0 alternates
([[T:evol_c7_period]], [[T:c7_center]]); its truncations to [−(7N+1), 7N+6] agree with it inside a shrinking cone
([[T:tr_agree]]). In the staged module <code>Rule30PeriodTwoCoupled</code>: c7 is the ether shifted by 4 cells
([[N:c7_eq_ether]], [[T:c7_ether_check]]); since B3 is black wherever B4 is ([[T:B4_imp_B3]]), the ether’s left
half is a ZBL orbit ([[T:etherLeft_zbl]]) satisfying the period-2 constraint with alternating free bits
([[T:ether_col1_black]], [[T:ether_free_bits]], [[T:etherLeft_eq_Theta]]); its right half is the half driven by the
alternating column ([[T:etherRight_drv]]); and the free bits are the complements of column 1 at the white steps
([[N:ether_coupled_witness]]). The synthesis script <code>ether_check.py</code> ([[C:C9]], re-run) gives the same facts
numerically.</p>

<h3 id="s4-skel">4.7 Skeletons</h3>
<p>Rank certificates with a designated bad class give eventual statements: if c = w<sup>∞</sup>, the true strip
eventually stays in the bad class ([[T:sk1_sound_bad]]), so every predicate checked on that class holds eventually
([[T:sk1_eventually_pred]]). With kernel-checked certificates ([[T:K0001_checkb]]–[[T:K0011_badImp]]):</p>
<ul>
<li>[[N:skeleton_0001]], [[N:skeleton_0001_explicit]]: under 0001, eventually column 1 = 0 and column 3 = 1 at
phase 0, column 2 = 1 at phase 1, column 1 = 1 at phase 2, column 1 = 1 and column 2 = 0 at phase 3; column −1 is
(0, = column 1, 0, 1).</li>
<li>[[N:no11_0001]]: under 0001, eventually a black column-1 cell at phase 1 is followed four steps later by a white
one.</li>
<li>[[N:skeleton_0011]], [[N:skeleton_0011_explicit]]: under 0011, eventually column 1 is black at phases 1, 2 and
white at phase 3; column −1 is (= column 1, 0, 0, 1). An independent hand proof without certificates gives the same
statement ([[N:direct_skel]]).</li>
<li>[[N:column_m1_0111]]: under 0111, for all t ≥ T, column −1 is (= ¬column 1, 0, 0, 1); no skeleton is needed.</li>
</ul>

<h3 id="s4-dl">4.8 The driven left half</h3>
<p>For any driver, the edge of a finite nonzero left start moves left one cell per step ([[T:dl_edge]]), so Jen’s
argument runs inside the half-line: two adjacent columns are never both eventually periodic
([[T:dl_adjacent]]), and with an eventually periodic driver no column q &lt; 0 is eventually periodic
([[N:dl_no_periodic_column]]). The left half therefore has no absorbing words; the absorbing-word route works only on
the right. The real left half is the driven half from any time T, with the real center or with the effective
boundary ([[T:dl_cell_eq_L]], [[N:dl_cell_eq_L_eff]]).</p>

<h3 id="s4-rp">4.9 Right-diagonal period theory</h3>
<p>Write e<sub>j</sub> for the least e with R<sub>j</sub> of period 2<sup>e</sup> ([[T:rp_exists_IsE]]). Periods are
monotone ([[T:rp_per_mono_all]]) and obey the doubling rule e<sub>j+1</sub> = e<sub>j</sub> + [R<sub>j+1</sub>(2<sup>e<sub>j</sub></sup>) = 1]
([[N:rp_e_step]]); when the period doubles, a half-period shift complements the diagonal and every period window
is exactly half black ([[T:rp_antiperiod]], [[T:rp_half_black]]); e<sub>j</sub> − e<sub>j−1</sub> is the parity of the
input over one period ([[T:rp_S_rule]]); the period never doubles three times in a row ([[T:rp_no_three]]).
Bounds: every period of R<sub>j</sub> exceeds ⌈j/2⌉ ([[T:rp_period_gt]]); j ≤ 2<sup>e<sub>j</sub>+1</sup> − 2
([[T:rp_per_bound]]); e<sub>j</sub> ≤ ⌊(2j+1)/3⌋ ([[N:rp_per_upper]]); the guess e<sub>j</sub> ≥ ⌊j/2⌋ is false
([[T:rp_not_half_lower]]). Rows at powers of two restart the pattern at the right edge ([[N:rp_rows_at_powers_of_two]],
[[T:rp_row_restart]], [[T:rp_center_restart]], [[T:rp_column_continuity]]). A black center cell lies inside the
first period of its diagonal ([[T:rp_center_black_lt]]). None of this reaches c(t) = R<sub>t</sub>(t) directly.</p>
</section>
"""

S5 = r"""
<section id="s5">
<h2><span class="secno">5</span> Barrier theorems and their exact scope</h2>
<p class="lead">A barrier says that a class of arguments cannot succeed. Each one below is {{chip:ok}} in Lean except
§5.4, and each is stated with the class it rules out and the witnesses it uses.</p>

<h3 id="s5-q01">5.1 Q01-only barriers</h3>
<p>Setting: the ZBL <code>z</code>, a double step G = Z², and a surviving double step of a finite start (depth 1
black at times 0 and 2). The truncated stripe trunc n (black at odd depths ≤ n) keeps depth 1 black at every
t ≤ n and dies at n + 1 ([[N:trunc_survives]]), so constrained runs from finite starts are arbitrarily long.</p>
<ul>
<li>B1 ([[N:lasso]], [[T:lasso_gen]]): every abstraction of states into a finite set repeats a value along one
surviving truncated-stripe run; hence every sound finite abstract transition relation has a reachable cycle
([[T:reachable_cycle]]), and no ranking through a finite abstraction decreases along all surviving double steps
([[N:no_finite_abstract_ranking]]).</li>
<li>B2 ([[N:no_local_ranking]]): no function of (width, wall window of any fixed size, edge window of any fixed
size) into ℕ decreases strictly along every surviving double step of every finite start.</li>
<li>B6 ([[N:no_edge_dfa]]): no finite automaton, of any size, reading the row from its edge defines such a ranking
through its longest accepted prefix.</li>
<li>{{chip:comp}} Reading from the wall instead: no automaton with ≤ 5 states works on 28 recorded surviving pairs
(z3 UNSAT, re-checked in this pass, [[C:C8]]).</li>
</ul>
<p><b>Scope.</b> These theorems rule out proofs of Q01 by these methods, that is, proofs that use the left half
alone with unconstrained free bits. Every witness is a truncated stripe, whose free bits are 1 for about n/2
consecutive white steps. A real period-2 history also satisfies the right-half law “no 11111”
({{chip:ok}} [[N:col1_black_among_five]]), which these witnesses violate, so the barriers do not apply to arguments for CQ01 or for period 2 that
use the right half. Whether analogous barriers hold for CQ01 is open; §5.2 is the two-sided result available now.</p>

<h3 id="s5-joint">5.2 The two-sided JointBarrier</h3>
<p>[[N:no_joint_local_ranking]]: there is no R(lo, hi, center window, left-edge window, right-edge window) ∈ ℕ,
for any fixed window sizes, that strictly decreases at every step where the center flips, over all finite
configurations of the full line (lo and hi are the leftmost and rightmost black cells). The witnesses are the
truncations of c7 (§4.6): genuine finite rule-30 configurations, both halves included, whose center alternates for
about 7N steps. <b>Scope.</b> It rules out ranking functions that see only the two widths and bounded windows at the
center and the two edges, uniformly over all finite configurations. It does not rule out arguments that use
unbounded or global information (whole rows, counts over the row, diagonal periods) or that use the exact single
seed rather than every finite configuration.</p>

<h3 id="s5-edge">5.3 The edge-region barrier</h3>
<p>[[N:edge_region_barrier]]: for any far part z (edge at depth m − 1), any prescribed values c of column −1 and any
d ≤ m, some row agrees with z from depth d on, has the same edge region as z at every time, and has column −1 equal
to c up to time d − 1 ([[T:complete_near_wall]], [[T:far_light_cone]]). So the left-edge structure, including all
eventually periodic left diagonals there, together with the wall constraint on a window shorter than the distance to
the edge, yields no contradiction. The round-1 versions: on the driven left half, for every driver, n ≥ 1 and target
b, exactly one start with edge at −n has column −1 = b at steps 0..n−2 ([[N:barrier_exists]], [[T:barrier_unique]]);
for an arbitrary configuration, every column is realizable with any right half, uniquely
([[N:column_realizable_unique]]); and agreeing with the seed on p ≥ −n does not prevent an eventually white center
([[N:seed_perturbation]]). Finally rules 90, 150 and 210 satisfy the generalized Jen theorem
([[T:run_not_adjacent]]) but have eventually periodic single-seed centers ([[N:rz_barrier]]). <b>Scope.</b> A proof of
Problem 1 must use rule 30’s ∨ and the finiteness of the far left of the seed, and a window argument must look past
time 2T − 1 when the onset is T.</p>

<h3 id="s5-cons">5.4 The additive / conservation-law barrier</h3>
<p>{{chip:paper}} An additive quantity Φ(x) = Σ<sub>k</sub> h(x<sub>k</sub> … x<sub>k+r−1</sub>) of range r is conserved by a
cellular automaton F on all finite (equivalently, all spatially periodic) configurations exactly when
h ∘ F − h ∘ mid is a coboundary on the de Bruijn graph of words of length r + 2·radius; the trivial laws (constants
and coboundaries) form a space of dimension 2<sup>r−1</sup>. This standard criterion (Hattori and Takesue 1991) turns
the existence of a nontrivial law of range r into a finite rank computation. The round-2 write-up of the paper
argument is not stored in the shared directory; the criterion is stated here as it is used by the programs.</p>
<p>{{chip:comp}} Result ([[C:C6]], three independent methods, re-run in this pass): rule 30 has no nontrivial additive
conservation law of range r ≤ 10; rule 30² has none of range r ≤ 8; and rule 30² has no nontrivial period-2
alternating law Σ (−1)<sup>k</sup> h(…) of range r ≤ 9. Full rank modulo a prime certifies full rank over ℚ.
<b>Scope.</b> This excludes proofs based on an exactly conserved additive quantity of these ranges. It says nothing
about larger ranges, inequalities (monovariants, §7.3) or non-additive invariants.</p>
</section>
"""

S6_HEAD = r"""
<section id="s6">
<h2><span class="secno">6</span> Computational facts</h2>
<p class="lead">Nothing in this section is a proof. Each fact names its program, says whether it was cross-validated
by an independent code, and says what was re-run in this pass. The full list is the <a href="#computations">computation
index</a>.</p>
"""

S6_DW_TEXT = r"""
<h3 id="s6-dw">6.1 D(W) ≤ 2W + 8 for W ≤ 71</h3>
<p>D(W) is the largest first-violation time over ZBL rows supported on depths 1..W (§1.2). Every such row dies
(Q01 holds for them), and the bound D(W) ≤ 2W + 8 holds for every W ≤ 71, with equality only at W = 11
(D = 30). D(71) = 128. This is the quantitative side of BWR: the optimal bound in [[T:Q01_iff_bounded]] is
governed by the largest survival time over supports ≤ d. For W ≤ 16 the statement is a Lean theorem
([[T:q01_width_le_16]]: death before time 34).</p>
"""

S6_DW_AFTER = r"""
<p><b>Programs and cross-validation</b> ([[C:C1]]). Four codes written independently by four round-2 agents:
<code>A-reconmap/c/zt2.c</code> (breadth-first frontier with deduplication, then depth-first; all W ≤ 71, re-run in
this pass with up to 64 chunks), <code>progA-backdet/dfs.c</code> (stored table, W ≤ 58),
<code>A-invsearch/maxdeath2.c</code> (stored table, W ≤ 40) and <code>A-monovariant/dfs.c</code> (re-run in this pass for
W ≤ 40 and W = 50, 56, 58). They agree at every overlapping width. Widths 59–71 rest on zt2 alone. Restricted variants
(free bits constrained by golden, no-11111 or the block law) were also computed by two codes, but with different
conventions for the initial run; their tables disagree at several widths and are not used here.</p>
"""

S6_REST = r"""
<h3 id="s6-stripe">6.2 Stripe-prefix families</h3>
<p>The family S[1..m] · v · 0<sup>∞</sup> (the stripe on depths 1..m, then a word v, then white) is infinite in m.
Ahead of the first deviation the row is the stripe, so a window of K cells behind the front evolves autonomously
while the front walks to the wall; its orbit is eventually periodic, so every m is covered by finitely many arrival
states. <b>Result</b> ([[C:C2]]): for every v of length ≤ 7 and every m, the run dies within at most 45 steps after
the front arrives, so by time m + |v| + O(1). For length 8, four words (least significant bit first: 11000001,
11110001, 10010011, 10111101) are inconclusive in at least one certifier at the window sizes tried; front_cert
certifies 10111101 with a 64-cell window. <b>Programs:</b>
<code>A-invsearch/front_cert.c</code> (Brent cycle detection on the front window) and <code>A-monovariant/family.c</code>
(moving-frame bijection), two independent certifiers that agree; each checked against direct simulation
(<code>front_validate.py</code>: 300 random (m, v), all agree; <code>family_validate.py</code>: 0 mismatches). Re-run in
this pass: family.c for tails ≤ 8 and both validators.</p>

<h3 id="s6-absorb">6.3 Absorption evidence for period 4</h3>
<p><b>Result</b> ([[C:C3]]): for each of 0001, 0011, 0111, with the 109-state wall exactly as in Lean
(<code>B-edge-trap/wallmin_13.bin</code> equals <code>wallStates</code>; checked in this pass), every one of the following
right halves enters the ether-and-wall family within 20000 steps:</p>
<div class="tframe"><table class="numtab">
<thead><tr><th>w</th><th>true right halves, T = 1..5000, 4 phases</th><th>max entry delay</th><th>all 2<sup>16</sup> center prefixes, 4 phases</th><th>max entry delay</th></tr></thead>
<tbody>
<tr><td>0001</td><td>20,000 / 20,000 enter</td><td>825</td><td>262,144 / 262,144 enter</td><td>792</td></tr>
<tr><td>0011</td><td>20,000 / 20,000 enter</td><td>1,434</td><td>262,144 / 262,144 enter</td><td>1,627</td></tr>
<tr><td>0111</td><td>20,000 / 20,000 enter</td><td>525</td><td>262,144 / 262,144 enter</td><td>547</td></tr>
</tbody></table></div>
<p><b>Programs:</b> <code>B-edge-trap/entry2.c</code>; cross-checked by an independent Python implementation of Lean’s
<code>InFamily</code> (<code>writeup-r2/absorb/infamily_check.py</code>), which reproduces entry2’s entry delays exactly on
nine (w, T) cases. Two further observations: configurations built to stay 1000 steps in the bad strongly connected
component of the width-11 to 13 strip relaxation are absorbed by consistent closures of width 24–28 within 175–400
steps (<code>progB-avoid/check_surv.py</code>, re-run); and for the period-2 word 0101 the same family is not
absorbing (11,630 of 12,000 true right halves fail to enter, stored result <code>B-edge-trap/p2_true.txt</code>, not
re-run). Absorption is not forced at any fixed width: the strip relaxations have bad components at every width
tried (b ≤ 22 for 0001, b ≤ 18 for 0011 and 0111, growth 1.48–1.58 per step; <code>progB-avoid/scc_an.c</code>,
stored, not cross-validated), so a proof must use that the true right half is finitely supported.</p>

<h3 id="s6-block">6.4 The period-2 right-half block law and the density 3/14</h3>
<p>Drive the right half by an alternating center and record column 1 at the white steps; under a real period 2
these values are the complements of the free bits. <b>Result</b> ([[C:C4]]): after a transient of at most 27
samples in every run tried, every gap between consecutive 1s is 3 or 5, so the output is a concatenation of the
blocks 100 and 10000. In the synthesis run (true right half at T₀ = 2000, phase 0, 98,000 samples) there are 3,509 gaps of 3 and
17,493 of 5, and 21,003 ones against 3n/14 = 21,000. Every window of 14 consecutive samples holds 3 ± 1 ones, every
window of 140 holds 30 ± 2, and the prefix discrepancy stays in [−7.6, 14.4]; a random finite right half gives
[−11.0, 21.8]. The 3-blocks are not periodically placed: the number of 5-gaps between consecutive 3-gaps ranges from
1 to 31. Factor complexity: p(8) = 10, p(16) = 23, p(32) = 92, p(64) = 702, p(128) = 15,960, p(192) = 72,852,
p(256) = 95,451, and from length 384 on every factor occurs only once in the sample.</p>
<p><b>Programs:</b> <code>synth-r2/rc3.c</code>, <code>rc4.c</code>, <code>rc5.c</code>; <code>synth-r2/y_out.txt</code> is
reproduced byte for byte by <code>rc5 2000 200000 0 0</code> in this pass. Cross-validated by
<code>writeup-r2/yindep.py</code>, an independent Python implementation: six runs (true right halves at T₀ = 777, 2000,
3000 in both phases, and two random right halves) show only gaps 3 and 5 and densities 0.2136–0.2149. If the law holds
for every finite right half, f eventually lies in {011, 01111}<sup>∞</sup> and every epoch depth in {6, 10} (§3.1).
The law is not a consequence of a narrow strip: in the strip relaxation (column b+1 arbitrary), the limit set of
reachable states still admits gaps 2 and 4 for every width b ≤ 12, while gap 1 is never possible and gaps ≥ 6 are
impossible from b = 4 on (<code>writeup-r2/blocklaw_strip.py</code>, single code). Like absorption, it depends on the
right half not being adversarial.
The third-party notes of §8 describe this column differently, as a coded rotation with kicks; the two descriptions
were not compared quantitatively.</p>

<h3 id="s6-other">6.5 Other computations used in this report</h3>
<ul>
<li>No 11111 ([[C:C5]]): <code>A-invsearch/rightstrip.c</code> and <code>writeup-r2/five_white.py</code> agree that the width-4
strip relaxation allows at most 4 consecutive white column-1 values at white steps, while widths 1–3 allow more. The
statement is now also a Lean theorem ([[T:col1_black_among_five]]).</li>
<li>Conservation laws ([[C:C6]]), monovariants ([[C:C7]]), automaton rankings ([[C:C8]]), ether and relay checks
([[C:C9]], [[C:C10]]): see §5.4, §7.</li>
</ul>
</section>
"""

S7 = r"""
<section id="s7">
<h2><span class="secno">7</span> Refuted claims</h2>

<h3 id="s7-trap">7.1 The round-1 single-trap claim: two refutations, one phenomenon</h3>
<p>Round 1 certified, for each w ∈ {0001, 0011, 0111}, a trap S<sub>w</sub> of the strip relaxation (width 16, 16, 14)
inside which column 1 at the white phases is periodic, and observed that random finite right halves always enter it.
The claim that every finite right half enters S<sub>w</sub> would have excluded least period 4. It is false.</p>
<ul>
<li>{{chip:ok}} [[N:never_S0001]], [[T:never_S0011]], [[T:never_S0111]]: explicit finite right halves (ether on columns
1..k, a wall state on the next 13 columns, white beyond) never enter S<sub>w</sub>; they stay pure ether forever
([[T:config_pure_ether]]).</li>
<li>{{chip:comp}} The relay configuration of progB-avoid (columns 4 and 7 black, driver 0001, phase 1) never enters
S<sub>0001</sub>: at t = 300 its width-24 strip state has a closed forward closure of 188 states, consistently
labelled (column 1 at white phases periodic, word 010) and disjoint from S<sub>0001</sub> after projection, and the run
never visited S<sub>0001</sub> before ([[C:C10]], <code>progB-avoid/verify_relay.py</code>, re-run).</li>
<li><b>One phenomenon.</b> <code>synth-r2/relay_family.py</code> (re-run) shows that the relay configuration enters the
ether-and-wall family at t₁ = 159 (alignment j0 = 6, k = 10), while the Lean counterexamples are family members from
the start. Both are absorbed, into deeper members of the infinite family rather than into a fixed-width trap. This is
why Absorption(w) is stated over the whole family.</li>
</ul>

<h3 id="s7-lowc">7.2 Low-complexity certificates</h3>
<ul>
<li>{{chip:comp}} The right-half output beside an alternating center is not a low-complexity sequence: p(64) = 702
where a Sturmian or rotation coding has 65, and every factor of length 384 or more occurs only once in the
98,000-sample run ([[C:C4]]). Certificates that need column 1 to be a rotation coding or the output of a small automaton cannot
apply to it as such. This is a finite-sample measurement, not a proof of positive entropy.</li>
<li>{{chip:ok}} Finite-state ranking certificates for Q01 do not exist (B1, B6 in §5.1); {{chip:comp}} none with ≤ 5
states reads from the wall ([[C:C8]]).</li>
<li>{{chip:comp}} Fixed-width strip certificates of the round-1 kind cannot exclude 0001, 0011 or 0111: at every width
tried the relaxation has a bad component that adversarial inputs never leave (§6.3).</li>
</ul>

<h3 id="s7-mono">7.3 Simple monovariants</h3>
<p>{{chip:comp}} <code>A-monovariant/mono.c</code> ([[C:C7]], re-run) follows every surviving double step of every finite
start of width ≤ 22 (2,097,275 transitions) and records the change of 15 quantities: weight, walls (all, 00, 11, by
parity class), first defect position, defects against the stripe, runs of ones, weights at odd and even positions,
first class-1 wall, class-1 defects, zero runs and 11 pairs. Every one of them both increases and decreases, so none is
a monovariant. Exact additive conservation laws of range ≤ 8–10 do not exist either (§5.4). Not cross-validated by a
second code.</p>

<h3 id="s7-corr">7.4 Corrected statements</h3>
<ul>
<li>The prose of <code>ZBL.alt_first_defect_parity</code> holds for the phase c(T) = 0 only;
[[T:alt_other_phase]] proves the other-phase reading false and [[T:alt_first_defect_phase]] is the phase-free form.</li>
<li>The B1 prose bound j ≤ 2<sup>w</sup> + 1 was off by one ([[T:prose_off_by_one]]); the Lean proof uses j ≤ 2<sup>w</sup>.</li>
</ul>
</section>
"""

S8 = r"""
<section id="s8">
<h2><span class="secno">8</span> Relation to prior and third-party work</h2>
<p class="lead">{{chip:third}} marks a claim from outside this project. Unless a row says it was re-checked, it was not
verified here. Summaries come from <code>lit-recent/NOTES.txt</code> and <code>lit-oss/</code>; downloaded files were read
as text only.</p>
<div class="tframe"><table class="littab"><colgroup><col class="l-work"><col class="l-claim"><col class="l-rel"><col class="l-stat"></colgroup>
<thead><tr><th>Work</th><th>Claim</th><th>Relation to this project</th><th>Status here</th></tr></thead>
<tbody>
<tr><td>Jen 1986, J. Stat. Phys. 43</td><td>No two columns of the single-seed pattern are both eventually periodic.</td><td>Proved in Lean ([[T:jen]]); masked, window, clock and driven-half forms are new refinements.</td><td><span class="chip ok">proved</span></td></tr>
<tr><td>Jen 1990, Physica D 45, Prop. 3</td><td>For left-injective rules with 001 ↦ 1 (30, 86, 90, 150, 210, …), at most one eventually periodic column from any finite initial condition.</td><td>Single-seed case in Lean; the driven-left-half version ([[T:dl_adjacent]]) covers finite left starts; the general finite-configuration statement is not formalized.</td><td><span class="chip third">third-party</span> beyond the single seed</td></tr>
<tr><td>Rowland 2006, Complex Systems 16</td><td>Right diagonals purely periodic with 2-power periods; left-diagonal doubling criterion.</td><td>Right side reproved and extended ([[T:R_periodic]], §4.9); the left criterion is not formalized.</td><td>right side <span class="chip ok">proved</span></td></tr>
<tr><td>Kopra 2023, TCS 946</td><td>Rapid left expansivity: width-2 traces of number-like configurations are not eventually periodic; rule 90 shows width 1 cannot follow.</td><td>Consistent with [[T:rz_barrier]], proved here for rules 90, 150, 210.</td><td><span class="chip third">third-party</span></td></tr>
<tr><td>Condrey, arXiv 2609.09431</td><td>No column of a nonzero finite configuration is eventually constant; sharp constant-prefix horizon w + 2; period 2 named as the next open case; no bounded-horizon law at period 2.</td><td>Our Lean period-1 result covers only the single seed ([[T:no_column_const]]). The fibre theorems were spot-checked on 300 random right halves in round 1 (<code>lit-recent/scripts/check_condrey.py</code>). The horizon remark parallels §5.3.</td><td><span class="chip third">third-party</span>, spot-checked</td></tr>
<tr><td>Nersissian, arXiv 2609.25077</td><td>Newton supports of the diagonals; first contact ⌊m/2⌋; Fibonacci ceiling; right-diagonal least period ≥ ⌊m/2⌋ + 1; left profile bound m + 2 ≤ 4<sup>Q<sub>m</sub></sup>.</td><td>Same flavour as [[T:rp_period_gt]], [[T:rp_per_bound]]. Recurrences and bounds checked numerically for m ≤ 24 in round 1.</td><td><span class="chip third">third-party</span>, spot-checked</td></tr>
<tr><td>Nersissian, arXiv 2609.25078</td><td>Integer lift with deg D<sub>k</sub> = F<sub>k+2</sub> − 1, so right-diagonal periods divide 2<sup>⌈log₂ F<sub>k+2</sub>⌉</sup> ≈ 2<sup>0.694k</sup>.</td><td>The Lean bound e<sub>j</sub> ≤ ⌊(2j+1)/3⌋ ([[T:rp_per_upper]]) is asymptotically sharper (indices differ by one).</td><td><span class="chip third">third-party</span></td></tr>
<tr><td>ghywel/placego notes (to 2026-10-14)</td><td>Period-by-period programme for all finite configurations; chain period 2 ⟸ B ⟸ LR<sub>m</sub> ⟸ LR ⟺ “R(d) finite for all d” (König); doubling conjecture R(d) ≤ d + 4, reported exact to depth 89; “Theorem A, Jen with a clock”; Theorem E (a Sturmian column 1 never gives a finite forced left half); column 1 beside 0101… described as a rotation by 17/56 kicked in notches of 1/28 turn; a joint halt of the project on 2026-10-14.</td><td>LR is our LR ([[T:Q01_iff_LR]]); their R(d) finiteness has the shape of BWR ([[T:Q01_iff_bounded]]); our Lean [[T:jen_clock]] is a clock form of Jen of the same kind; §6.4 measures the same column at the white steps (gaps 3 and 5, density 3/14). Index conventions were not reconciled, and their numbers were not re-run.</td><td><span class="chip third">third-party</span></td></tr>
<tr><td>Other repositories (Patto1155/rule30-foundry, nateberzai, cochon123, Dibujaron)</td><td>Word-specific exclusions and SAT horizons.</td><td>None excludes period 2 (round-1 survey).</td><td><span class="chip third">third-party</span></td></tr>
<tr><td>Claimed solutions (Das 2022, others)</td><td>Heuristic or claimed proofs of Problem 1.</td><td>None found rigorous in round 1.</td><td><span class="chip ref">not accepted</span></td></tr>
</tbody></table></div>
</section>
"""

S9 = r"""
<section id="s9">
<h2><span class="secno">9</span> The open frontier and an honest assessment</h2>
<h3 id="s9-where">9.1 Where things stand</h3>
<ul>
<li><b>Problem 1 is open.</b> The only period excluded for all its words is 1. The other unconditional exclusions are
specific: 32 certified words, families defined by long black runs (Theorems B, B′, D, the long-runs theorem, 0 1<sup>k</sup>,
0<sup>r</sup>11), and T + P ≥ 16359.</li>
<li><b>Period 2</b> is reduced to Q01 and to the weaker CQ01; neither reduction is an equivalence. Q01 is a clean
statement about a deterministic system that is conjugate to the full shift on its free bits; it is supported by D(W) ≤ 2W + 8 up to W = 71 and by the
epoch structure, and it is open. CQ01 is weaker and therefore easier in principle; the right-half laws (no 00 and no
11111 proved, block law observed) are the extra structure it offers.</li>
<li><b>Least period 4</b> reduces to Absorption(w) and to C3(w), both in Lean. Absorption is supported by every run
tried; no fixed-width argument can prove it, because adversarial strips avoid every trap.</li>
<li><b>Least period 3</b> (001, 011) has no reduction recorded in the round-2 sources. For 001 the effective boundary
is identically white, so the left half is again the ZBL; for 011 it is 010; <code>synth-lead/p3_affine.py</code> checks a
hand-derived affine structure of the left columns numerically, while a simple reachability check
(<code>synth-lead/c8check.py</code>) does not force column 1 at widths 6–10.</li>
</ul>
<h3 id="s9-cond">9.2 Conditional results, with hypotheses</h3>
<div class="tframe"><table class="numtab">
<thead><tr><th>Hypothesis (open)</th><th>Conclusion</th><th>Status of the implication</th></tr></thead>
<tbody>
<tr><td>Q01 (any of its four forms)</td><td>c is not eventually 2-periodic</td><td>{{chip:impl}} [[T:p2_of_Q01]], [[T:no_eventual_period_two]], [[T:no_period_two_of_Q01]]</td></tr>
<tr><td>CQ01 (implied by Q01, [[T:CQ01_of_Q01]])</td><td>c is not eventually 2-periodic</td><td>{{chip:impl}} [[T:p2_of_CQ01]]</td></tr>
<tr><td>Absorption(0001), Absorption(0011), Absorption(0111)</td><td>c has no least period 4</td><td>{{chip:impl}} [[T:lp4_absorption]]</td></tr>
<tr><td>C3(0001), C3(0011), C3(0111)</td><td>c has no least period 4</td><td>{{chip:impl}} [[T:lp4_C3]]</td></tr>
<tr><td>Q01</td><td>uniform death time for each width; phase-1 version</td><td>{{chip:impl}} [[T:uniform_death]], [[T:Q01_phase1]]</td></tr>
</tbody></table></div>
<h3 id="s9-next">9.3 The most promising next steps</h3>
<ol>
<li>Add the seven staged modules to the catalog. The integration task has formalized C3(w) ⇒ exclusion, CQ01 and
both of its implications, no-11111 and the stripe corollary; this pass compiled the modules from source and printed
the axioms of all their theorems (§C). What remains is the import into <code>Ruliology.lean</code>.</li>
<li>Prove the right-half block law, or any law that bounds the epoch depths, for every finite right half driven by an
alternating center. Combined with §4.3 it would confine a period-2 history to epochs of depth 6 and 10.</li>
<li>Attack CQ01 with global information on both sides. §5 shows that rankings built from local data at the wall, the
center and the edges cannot suffice; the right edge carries rigid global structure (§4.9) that no barrier excludes.</li>
<li>Prove Absorption for one word. 0111 has a single alignment, needs no skeleton ([[T:column_m1_0111]]) and has the
shortest observed entry delays.</li>
<li>Re-check or formalize the most useful third-party statements: Condrey’s fibre theorem would extend the period-1
exclusion to all finite configurations, a natural base for the all-finite-configuration versions of CQ01.</li>
</ol>
<h3 id="s9-honest">9.4 Assessment</h3>
<p>The work so far has turned Problem 1 into precise, checkable sub-questions and has shown where several natural
methods must fail. It has not produced a method that excludes any period ≥ 2 outright. Every reduction ends in a
statement of the same kind as the original: a finitely supported configuration cannot sustain a shift-invariant
constraint forever. The evidence for Q01 and Absorption is strong and consistent across independent codes, but
round 1 already found that survival in the ZBL behaves like a random-constraint model, so the evidence does not point
to a short proof. The barrier theorems narrow the search: ranking functions and finite abstractions built from local
data fail for the left half alone and for bounded windows at the center and both edges, so a proof of period-2
exclusion needs non-local information, most plausibly from both halves; a proof of period-4 exclusion must use the
finite support of the right half rather than any fixed-width trap. Progress on period 2 or period 4 alone would be a genuine partial result toward Problem 1; it
would not by itself settle it.</p>
</section>
"""
