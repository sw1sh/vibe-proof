export const meta = {
  name: 'rule30-p1-round1',
  description: 'Rule 30 Prize Problem 1: literature sweep + 8 independent attack angles + adversarial verification + synthesis',
  phases: [
    { title: 'Literature', detail: '5 parallel literature/prior-art readers' },
    { title: 'Theory', detail: '8 independent proof-strategy agents with experiments' },
    { title: 'Verify', detail: 'adversarial verification of claimed results' },
    { title: 'Synthesize', detail: 'status report and round-2 plan' },
  ],
}

const BRIEF = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/BRIEF.md'
const COMMON = `First read the shared brief at ${BRIEF} (definitions, proven results, data, tools, and HARD constraints: every local command under 60 s via \`timeout 60\`, scratch files only under /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/<your-label>/, never modify the Ruliology repo or ruliology-lean/Ruliology/). Be rigorous and honest: never present an argument as a proof unless every step is justified; state gaps explicitly.`

const LIT_SCHEMA = { type: 'object', properties: {
  sources: { type: 'array', items: { type: 'object', properties: {
    title: { type: 'string' }, url: { type: 'string' }, what_it_proves: { type: 'string' },
    rigor: { type: 'string' }, relevance: { type: 'string' } },
    required: ['title', 'what_it_proves', 'rigor', 'relevance'] } },
  useful_theorems: { type: 'array', items: { type: 'string' } },
  claimed_solutions_assessment: { type: 'string' },
  summary: { type: 'string' } },
  required: ['sources', 'useful_theorems', 'summary'] }

const THEORY_SCHEMA = { type: 'object', properties: {
  angle: { type: 'string' },
  summary: { type: 'string' },
  claims: { type: 'array', items: { type: 'object', properties: {
    id: { type: 'string' },
    statement: { type: 'string' },
    status: { type: 'string', enum: ['proved', 'partially_proved', 'conjectured', 'refuted'] },
    significance: { type: 'string', enum: ['solves_problem_1', 'excludes_periods_for_all_transients', 'structural_lemma', 'computational_evidence', 'other'] },
    proof: { type: 'string' },
    evidence: { type: 'string' },
    lean_plan: { type: 'string' } },
    required: ['id', 'statement', 'status', 'significance', 'proof'] } },
  failed_approaches: { type: 'string' },
  most_promising_next_step: { type: 'string' } },
  required: ['angle', 'summary', 'claims', 'failed_approaches', 'most_promising_next_step'] }

const VERDICT_SCHEMA = { type: 'object', properties: {
  refuted: { type: 'boolean' },
  confidence: { type: 'string', enum: ['low', 'medium', 'high'] },
  gaps: { type: 'string' },
  counterexample_or_check: { type: 'string' },
  verdict_summary: { type: 'string' } },
  required: ['refuted', 'confidence', 'gaps', 'verdict_summary'] }

const SYNTH_SCHEMA = { type: 'object', properties: {
  status_of_problem_1: { type: 'string' },
  verified_results: { type: 'array', items: { type: 'object', properties: {
    statement: { type: 'string' }, proof_outline: { type: 'string' }, lean_target: { type: 'string' } },
    required: ['statement', 'proof_outline'] } },
  most_promising_directions: { type: 'array', items: { type: 'string' } },
  round2_plan: { type: 'array', items: { type: 'object', properties: {
    label: { type: 'string' }, prompt: { type: 'string' } }, required: ['label', 'prompt'] } },
  honest_assessment: { type: 'string' } },
  required: ['status_of_problem_1', 'verified_results', 'most_promising_directions', 'round2_plan', 'honest_assessment'] }

const LIT = [
  { label: 'lit-jen', prompt: `Literature task: Erica Jen's work on rule 30 and aperiodicity: "Global properties of cellular automata" (J. Stat. Phys. 43, 1986) and "Aperiodicity in one-dimensional cellular automata" (Physica D 45, 1990), plus any follow-ups citing them about temporal sequences/columns. Extract EXACT theorem statements about which columns (temporal sequences) of permutive or rule-30-like CA are aperiodic, under which initial conditions, and whether any result implies or nearly implies that the rule 30 center column (single seed) is not eventually periodic. Use web search/fetch; if a paper is paywalled, find abstracts, citing papers, reviews (MathSciNet/zbMATH), or theses quoting the results.` },
  { label: 'lit-claims', prompt: `Literature task: evaluate claimed solutions of the Rule 30 Prize problems: arXiv 2207.13237 "Rule 30: Solving the Chaos"; the ResearchGate "BHLM-Bas-Zeta Wolfram Project: Formal Resolutions of Wolfram-Family Open Problems"; any other arXiv/viXra/blog claims (search). For each, identify the claimed theorem, the key argument, and the precise fatal gap (or, if you find none, say so with care). Also check rule30prize.org / Wolfram writings for the official status of the prizes and any recognized partial results.` },
  { label: 'lit-recent', prompt: `Literature task: recent (2020-2026) mathematical work on rule 30's structure: arXiv 2604.00165 (Symmetric Nonlinear CA as Algebraic References for Rule 30), 2609.25077 and 2609.25078 (Nersissian, diagonal periods), Rowland "Local Nested Structure in Rule 30" (Complex Systems 16, 2006), and anything else on the center column, the left/right sides, diagonal periods, or partial results toward non-periodicity. Extract precise theorems and techniques that could be leveraged for Problem 1.` },
  { label: 'lit-repos', prompt: `Literature task: open-source partial-result efforts on the Rule 30 Prize: GitHub repos dcondrey/rule30 (may have moved or been renamed; search), beedbyte/rule30-research, fabianxvogt/rule30, Patto1155/rule30-foundry, and others you can find (search GitHub/code search via the gh CLI if available, and the web). For each, list rigorous partial theorems (e.g., excluded periods for ALL transients, structural lemmas), formal proofs (Lean/Coq/Isabelle), and computational certificates, with your assessment of rigor. Save any downloaded file in its own new directory under your scratch dir and never execute it.` },
  { label: 'lit-theory', prompt: `Literature task: general theory that might imply aperiodicity of a specific column of a one-dimensional CA orbit: permutive / bipermutive CA (Hedlund, Coven, Shereshevsky, Kurka, Blanchard-Maass, Nasu), expansivity and "temporal sequences", results on eventually periodic columns of CA orbits from finite seeds, nonlinear analogues of the automatic-sequence theory for linear CA (Allouche, Shallit, von Haeseler, Peitgen), entropy of columns, and results on rule 30 viewed as a stream cipher (Wolfram 1986, Meier-Staffelbach 1991, Koc-Apohan). Extract theorems with exact hypotheses that could apply to rule 30's center column.` },
]

const THEORY = [
  { label: 'absorbing-right', prompt: `Research angle "absorbing words, right half". For a binary period word w, drive the right half of rule 30 (cells p >= 1) at p = 0 by the periodic boundary c(t) = w[t mod |w|], starting from an ARBITRARY right-half configuration (also test configurations with the real pattern's right-edge structure: ones on p = t, zeros beyond). Determine experimentally for all words up to length ~10 (and random starts of widths up to a few thousand) which words force column 1 to be eventually periodic from EVERY start ("absorbing words"); the brief notes drivers 001, 0111, 0001, 0110 gave periodic column 1 from the seed. Then PROVE absorption for as many words as you can, with complete rigorous proofs: each absorbing word w excludes "c eventually w-periodic" for all transients, by Jen (columns 0 and 1). Identify the mechanism (e.g., OR-blocking: when c(t)=1, cell(t+1,1) = not(cell(t,1) or cell(t,2)); information flow rightward). Aim for a uniform theorem covering a large class of words (e.g., all words with property X), and say exactly which periods P are fully excluded (all words of period P).` },
  { label: 'absorbing-left', prompt: `Research angle "left half and the consistency at column 0". The left half evolves forward from c (boundary at p = 0), and consistency requires c(t+1) = cell(t,-1) xor (c(t) or cell(t,1)). In particular at times with c(t) = 1, cell(t,-1) = not c(t+1). For a periodic word w, study the left half driven by w from arbitrary left-half states with the left-edge structure (ones on p = -t, zeros beyond), and find words for which the forced values of column -1 (at times with c(t)=1) are incompatible with the left half's forward dynamics uniformly in the start state, or for which column -1 is forced eventually periodic. Give rigorous proofs of any T-independent exclusion; report experiments and exact failure points otherwise.` },
  { label: 'small-periods', prompt: `Research angle "exclude small periods for all transients". Focus on proving that the center column is not eventually periodic with period 2, then 3, 4, ... (for EVERY transient T). Combine any tools: the proven no-constant-column theorem (period 1), Jen's theorem, the column-0 constraints (c(t)=1 implies cell(t,-1) = not c(t+1); c(t)=0 implies c(t+1) = cell(t,-1) xor cell(t,1)), left-permutive reconstruction (cell(t,i-1) = cell(t+1,i) xor (cell(t,i) or cell(t,i+1))), driven halves, monotonicity arguments (when c is 0, cell(t+1,1) = cell(t,1) or cell(t,2)), finite-state/SAT arguments on strips, and the left/right edges. Note period-2 means c alternates eventually. Give complete proofs for any period you can exclude, or pinpoint precisely why each attempt fails.` },
  { label: 'diagonals', prompt: `Research angle "diagonal structure". Right diagonals R_j(t) = cell(t, t-j) are purely periodic with least period 2^{e_j} (data in brief); c(t) = R_t(t) = D_t(t); parity identity c(t) = parity #{s < t : cell(s,s-t+1) or cell(s,s-t+2)}; R_j(t) = R_j(t + k*2^{e_j}) so c(t) = cell(t + k*2^{e_t}, k*2^{e_t}); left diagonals eventually periodic with tiny periods and transients ~1.34 j. Seek an obstruction to eventual periodicity of c (or of special periods, e.g. powers of 2, odd periods) from these structures, or prove structural facts about e_j (e.g., e_j -> infinity, e_j >= floor(j/2)? bounds) that could feed such an argument. Rigorous proofs only; report experiments.` },
  { label: 'algebraic', prompt: `Research angle "algebra over GF(2)". Rule 30's ANF is l + c + r + c*r (mod 2). Relate rule 30 to linear rules (90, 150, 60, 102) whose center columns are 2-automatic, and to rules 86/135/149 (mirror/complement); explore polynomial / generating-function / Boolean-function-degree methods for the center column (e.g., the algebraic normal form of c(t) as a function of initial cells, degree growth, correlation immunity), and any algebraic invariant that an eventually periodic center column would violate. Also read arXiv 2604.00165 if useful. Rigorous results only; report experiments.` },
  { label: 'jen-generalized', prompt: `Research angle "generalize Jen". Jen's adjacent-column argument needs columns 0 and 1 both eventually periodic. Find the WEAKEST hypothesis that still yields a contradiction with the left edge via left-permutive reconstruction, e.g. "column 0 periodic and column 1 periodic only at times where column 0 is 0", or "column 1 eventually periodic up to a bounded/sparse set of exceptions", or "column 1 determined by a finite-state transducer of column 0". Then investigate whether the right half driven by an eventually periodic c must satisfy that weaker hypothesis (note: when c(t)=1 the next value of column 1 is not(cell(t,1) or cell(t,2)), when c(t)=0 it is cell(t,1) or cell(t,2)). Complete proofs for any lemma; precise failure analysis otherwise.` },
  { label: 'complexity', prompt: `Research angle "complexity and symbolic dynamics". Morse-Hedlund: c is eventually periodic iff its factor complexity p(n) <= n for some n. Explore whether structural properties (left-permutivity, the cone, diagonal periodicity, the driven-halves coupling) can force p(n) >= n+1 for all n, or force infinitely many distinct return words, or rule out eventual periodicity via recurrence/uniform-recurrence arguments. Also check symbolic-dynamics theorems (permutive/expansive CA, closing maps, Hedlund) for applicability to a single column of the single-seed orbit. Rigorous results only; experiments welcome.` },
  { label: 'new-ideas', prompt: `Research angle "new ideas, critically". Brainstorm genuinely new strategies for Problem 1 (potential functions on the cone, counting/entropy over the light cone, information-flow and causality arguments, renormalization or self-similarity of the left side, the regular left region left of p = -t/4 and its interface with the chaotic region, cryptanalytic structure, reductions to other open problems). For each idea, test quickly with experiments and try hard to make it rigorous; discard what fails. Deliver the 3 most promising concrete research programs with evidence and any rigorous partial lemmas you obtain.` },
]

phase('Literature')
const litPromise = parallel(LIT.map(l => () =>
  agent(`${COMMON}\n\n${l.prompt}\n\nReturn structured results.`, { label: l.label, phase: 'Literature', schema: LIT_SCHEMA })
    .then(r => r ? { ...r, label: l.label } : null)))

phase('Theory')
const VERIFY_SIGS = ['solves_problem_1', 'excludes_periods_for_all_transients']
const LENSES = [
  { key: 'rigor', text: 'Hunt for logical gaps, unjustified steps, hidden assumptions, misuse of definitions (e.g., confusing the driven system with the actual pattern, transient-dependence, quantifier order). Refute if any essential step is unproven.' },
  { key: 'counterexample', text: 'Try to falsify the statement and every intermediate lemma computationally (Python, under 60 s per run): random and adversarial instances, edge cases, exact definitions from the brief. Refute if any intermediate claim fails.' },
  { key: 'rederive', text: 'Independently reconstruct the full proof from the statement alone and the proof sketch. Refute if you cannot make every step rigorous yourself.' },
]
const theoryResults = await pipeline(THEORY,
  t => agent(`${COMMON}\n\n${t.prompt}\n\nReturn structured results. In "claims", include every rigorous result (with complete proofs in "proof") and every important conjecture or refutation (marked as such).`,
    { label: t.label, phase: 'Theory', schema: THEORY_SCHEMA }).then(r => r ? { ...r, label: t.label } : null),
  async (res) => {
    if (!res) return null
    const toCheck = (res.claims || []).filter(c => (c.status === 'proved' || c.status === 'partially_proved') && VERIFY_SIGS.includes(c.significance))
    const lemmas = (res.claims || []).filter(c => c.status === 'proved' && c.significance === 'structural_lemma')
    const big = toCheck.slice(0, 4), lem = lemmas.slice(0, 3)
    if (toCheck.length > 4) log(`${res.label}: verifying first 4 of ${toCheck.length} major claims`)
    if (lemmas.length > 3) log(`${res.label}: verifying first 3 of ${lemmas.length} lemmas`)
    const verifyOne = (c, lenses) => parallel(lenses.map(L => () =>
      agent(`${COMMON}\n\nAdversarial verification (lens: ${L.key}). ${L.text}\n\nCLAIM (${c.id}, from angle ${res.label}): ${c.statement}\n\nPROOF GIVEN:\n${c.proof}\n\nEVIDENCE GIVEN: ${c.evidence || '(none)'}\n\nDefault to refuted=true if you are not convinced every essential step is correct.`,
        { label: `verify:${res.label}:${c.id}:${L.key}`, phase: 'Verify', schema: VERDICT_SCHEMA })))
      .then(vs => {
        const v = vs.filter(Boolean)
        const notRef = v.filter(x => !x.refuted).length
        return { ...c, verdicts: v, survives: v.length > 0 && notRef * 2 > v.length }
      })
    const checkedBig = await parallel(big.map(c => () => verifyOne(c, LENSES)))
    const checkedLem = await parallel(lem.map(c => () => verifyOne(c, [LENSES[0]])))
    return { ...res, verified: [...checkedBig, ...checkedLem].filter(Boolean) }
  })

const lit = (await litPromise).filter(Boolean)
const theory = theoryResults.filter(Boolean)

phase('Synthesize')
const digest = JSON.stringify({ literature: lit, theory }, null, 1)
const synth = await agent(`${COMMON}\n\nYou are the synthesis lead for an attempt on Rule 30 Prize Problem 1. Below are all literature findings and theory results of round 1, including adversarial verification verdicts ("verified" entries; "survives" means a majority of verifiers did not refute). Produce: (1) the honest status of Problem 1; (2) the list of results that are genuinely established (survived verification, or are trivial/standard), each with a proof outline and a concrete Lean formalization target; (3) the most promising directions ranked; (4) a round-2 plan of 4-8 focused agent tasks (label + full prompt) that push the most promising directions, including any verification gaps to close; (5) an honest assessment of the chance of fully solving Problem 1 with these methods.\n\nROUND 1 DATA:\n${digest}`,
  { label: 'synthesis', phase: 'Synthesize', schema: SYNTH_SCHEMA })

return { synth, literature: lit, theory }
