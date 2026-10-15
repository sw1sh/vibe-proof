export const meta = {
  name: 'r30-archive-prepare',
  description: 'Audit the Rule 30 archive for what belongs in git, and add a buildable Lean snapshot of the catalog results, each adversarially checked',
  phases: [
    { title: 'Audit', detail: 'per-directory phase, purpose and exclusions (third-party, bulk, secrets)' },
    { title: 'Snapshot', detail: 'standalone lake project with byte-identical catalog modules' },
    { title: 'Check', detail: 'exclusion critic and snapshot verifier' },
  ],
}

const ARCH = '/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize'
const RES = `${ARCH}/research`
const CAT = '/Users/swish/src/wolfram/vibe-proof/ruliology-lean'
const TMP = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize'

const GROUPS = [
  { key: 'literature', dirs: ['literature', 'jen-lit', 'lit-oss', 'lit_theory', 'lit-recent'] },
  { key: 'coord-round1', dirs: ['scripts', 'window', 'driven', 'period2', 'absorb-right', 'generalize-jen', 'left-consistency', 'diagonal', 'smallperiods', 'gf2-algebra', 'complexity', 'newideas'], extra: 'Also cover the top-level files of research/: BRIEF.md, BRIEF2.md, FINDINGS-coordinator.md, consolidate_args.json, final_args.json, final_results.json, final_batch_results.json.' },
  { key: 'round1-verify', dirs: ['verify-noleftabs', 'verify-D-refined-jen', 'verify-bbarrier', 'verify-rows-pow2', 'verify-monostep', 'verify-C1-determination', 'mh-rigor-verify', 'verify-C2-window-jen', 'verify-restart-continuity', 'verify-driven-left-jen', 'verify-A-rightdiag-rigor', 'verify-constraintA', 'verify-c3-doubling', 'verify_mahler_rigor', 'verify-B-odometer-rigor', 'verify-C3-longones', 'verify-C4-smallperiods-rigor', 'verify-C4-counterexample', 'verify-C4-rederive', 'verify-C2-absorb9-rigor', 'verify-C5-rigor', 'verify-C1-effbdry-rigor', 'verify-longblack-rigor', 'verify-longblack-cx', 'verify-strip-cert-rederive', 'verify-longblack-rederive', 'verify-stripcert-cx', 'verify-thmD-rigor', 'verify-thmB-rigor', 'verify-bprime-cx', 'verify-Bprime-rigor', 'verify-strip-cert-rigor', 'verify-thmB-rederive', 'verify-theoremB-cx', 'verify-thmBprime-rederive', 'verify-thmD-cx', 'verify-thmD-rederive', 'verify-white0r11-rigor', 'verify-white0r11-cx', 'verify-maskedjen-rigor', 'verify-blackrunforcing-rigor', 'verify-p4traps-rigor', 'verify-white0r11-rederive', 'verify-cone-agree-rigor', 'verify-lemmaAstar-rigor', 'verify-lemmaA-nine-black-rigor'] },
  { key: 'round2', dirs: ['A-reconmap', 'A-monovariant', 'A-invsearch', 'progA-backdet', 'progB-avoid', 'B-edge-trap', 'synth-lead', 'V-etherwall-rigor', 'verify-B1-ether', 'verify-B1-rigor', 'verify-b2-rigor', 'verify-A1-rigor', 'verify-A2-rigor', 'verify-A1-zbl-rigor2', 'verify-A2-reconmap-rigor', 'V-A2-epochs-rigor', 'verify-A1reform-rigor', 'synth-r2', 'integrate-r2', 'writeup-r2'] },
  { key: 'final', dirs: ['final_tasks', 'kernel-certify-r2', 'p3-ether', 'integrate-final'] },
]

const AUDIT_SCHEMA = {
  type: 'object',
  properties: {
    dirs: { type: 'array', items: { type: 'object', properties: {
      dir: { type: 'string' },
      phase: { type: 'string', enum: ['coordinator', 'literature', 'round-1 attack', 'round-1 verification', 'round-1 curation', 'round-2 program', 'round-2 verification', 'round-2 synthesis', 'round-2 integration', 'round-2 write-up', 'final batch', 'final integration evidence', 'other'] },
      purpose: { type: 'string' },
      result: { type: 'string' } },
      required: ['dir', 'phase', 'purpose', 'result'] } },
    exclude: { type: 'array', items: { type: 'object', properties: {
      path: { type: 'string' },
      reason: { type: 'string', enum: ['third-party', 'bulk', 'secret', 'junk'] },
      note: { type: 'string' } },
      required: ['path', 'reason', 'note'] } },
    flags: { type: 'array', items: { type: 'string' } },
  },
  required: ['dirs', 'exclude', 'flags'],
}

const auditPrompt = g =>
  `Audit part of a research archive before it is committed to git. Archive: ${ARCH} (files under research/ were copied from a scratch area). It records a 2026-10-15 attempt on Rule 30 Prize Problem 1 by a coordinator and about 90 subagents:\n` +
  `- round 1: literature, attack angles, adversarial verifications, curation;\n` +
  `- round 2: program A (period 2 via the zero-boundary left half, Q01) and program B (least period 4 via traps and the ether), with verifications, synthesis, integration and a write-up;\n` +
  `- a final batch: kernel-certify-r2, p3-ether, and the catalog integration evidence in integrate-final.\n` +
  `Skim ${RES}/BRIEF.md and BRIEF2.md for context.\n\n` +
  `Your directories (under ${RES}/): ${g.dirs.join(', ')}. ${g.extra || ''}\n\n` +
  `Read-only: do not modify, move or delete anything, and do not run git. Wrap commands in \`timeout 60\`.\n\n` +
  `1. For each directory give its phase, what it was for (one line), and its main result (one honest line: proved in Lean, computational, refuted, or inconclusive).\n` +
  `2. List files that should NOT be committed, with exact paths relative to ${ARCH} (e.g. research/literature/das2022.txt) or tight globs:\n` +
  `   - third-party: text or OCR extracts of papers, books or web pages, and copies of files or theorem lists from third-party repositories. Keep our own notes about them and metadata such as titles, URLs and search-result listings.\n` +
  `   - bulk: generated data files over 250 KB that a script in the archive can regenerate; name the script. Keep smaller outputs, and keep any data file that a Lean file or a verification needs and that cannot be regenerated cheaply (say so).\n` +
  `   - secret: anything resembling credentials, tokens, private keys or personal data beyond the user's name in paths. Grep for api_key, token, secret, password, BEGIN .* PRIVATE KEY, ghp_ and sk-, and judge each hit.\n` +
  `   - junk: editor backups, empty files, OS files, binaries.\n` +
  `When unsure whether a .txt file is ours or third-party, open it and decide. Notes written by our agents and outputs of our programs are ours.\n` +
  `3. Put anything odd in flags.`

const SNAP_SCHEMA = {
  type: 'object',
  properties: {
    summary: { type: 'string' },
    modules_copied: { type: 'number' },
    hashes_match_catalog: { type: 'boolean' },
    build_ok: { type: 'boolean' },
    build_log: { type: 'array', items: { type: 'string' } },
    axioms: { type: 'array', items: { type: 'object', properties: { name: { type: 'string' }, axioms: { type: 'string' } }, required: ['name', 'axioms'] } },
    predating_modules: { type: 'array', items: { type: 'string' } },
    readme_written: { type: 'boolean' },
    readme_text: { type: 'string' },
    problems: { type: 'array', items: { type: 'string' } },
  },
  required: ['summary', 'modules_copied', 'hashes_match_catalog', 'build_ok', 'build_log', 'axioms', 'predating_modules', 'readme_written', 'readme_text', 'problems'],
}

const CRITIC_SCHEMA = {
  type: 'object',
  properties: {
    missed_third_party: { type: 'array', items: { type: 'string' } },
    wrongly_excluded: { type: 'array', items: { type: 'string' } },
    secrets_found: { type: 'array', items: { type: 'string' } },
    phase_corrections: { type: 'array', items: { type: 'string' } },
    notes: { type: 'string' },
  },
  required: ['missed_third_party', 'wrongly_excluded', 'secrets_found', 'phase_corrections', 'notes'],
}

const SNAPV_SCHEMA = {
  type: 'object',
  properties: {
    hashes_ok: { type: 'boolean' },
    root_ok: { type: 'boolean' },
    builds_ok: { type: 'boolean' },
    axioms_ok: { type: 'boolean' },
    readme_ok: { type: 'boolean' },
    refuted: { type: 'array', items: { type: 'string' } },
    overall: { type: 'string' },
  },
  required: ['hashes_ok', 'root_ok', 'builds_ok', 'axioms_ok', 'readme_ok', 'refuted', 'overall'],
}

const snapPrompt =
  `Create a standalone, buildable Lean snapshot of the Rule 30 Prize results at ${ARCH}/lean, so the user can read and build them from that folder, which is about to be tracked in git.\n\n` +
  `Source: the catalog at ${CAT}: lake project \`ruliology\`, lean-toolchain leanprover/lean4:v4.30.0, core Lean only, no dependencies. Its root Ruliology.lean imports 40 Rule30* modules. Their import closure is 54 modules: all Rule30* modules (including Ruliology/CellularAutomata/Rule30Certificates/) plus Ruliology.CellularAutomata.BusyBeaverLifetimes.\n\n` +
  `Do:\n` +
  `1. Copy the 54 closure modules byte-identically, keeping their paths (Ruliology/CellularAutomata/...). Do not edit them.\n` +
  `2. Add lean-toolchain (same as the catalog) and lakefile.toml with package name rule30prize, [[lean_lib]] name = "Ruliology", and defaultTargets = ["Ruliology"]. Add a root Ruliology.lean that imports exactly the 40 Rule30* modules the catalog root imports, in the same order. Give it a module docstring: this is a snapshot of the ruliology-lean catalog taken on 2026-10-15, with the hash manifest in SHA256SUMS.\n` +
  `3. Write lean/SHA256SUMS for the copied modules (\`shasum -a 256\`, paths relative to lean/). Confirm every hash equals the catalog file's hash.\n` +
  `4. Build module by module in dependency order, one at a time: \`timeout 60 lake build Ruliology.CellularAutomata.<M>\` from lean/. Never run two Lean or lake processes at once; the machine is short on memory. The 4 Rule30Certificates/ZeroBoundaryWidth52Chunks* modules take about 20 s and 3.1 GB each. Then run \`timeout 60 lake build\`. Record the times.\n` +
  `5. Under ${TMP}/snapshot/ (outside the archive), compile a scratch file with \`lake env lean\` from lean/ that runs #print axioms on the headline theorems, finding their exact names in the sources:\n` +
  `   - period 1: Rule30Prize.center_not_eventually_period_one and no_column_eventually_constant;\n` +
  `   - the main theorems of Rule30Window, Rule30FactorWindow and Rule30PeriodTwo (Q01 implies no period 2);\n` +
  `   - Rule30ZeroBoundaryWidth52.q01_width_le_52;\n` +
  `   - Rule30EtherTrap.pure_ether_not_in_trap_0001, _0011 and _0111;\n` +
  `   - Rule30PeriodTwoWidth6.free_bit_constraints;\n` +
  `   - Rule30Ether's absorption theorem;\n` +
  `   - Rule30EtherThree.no_wall_le_12, not_eventually_001_of_absorption and not_eventually_011_of_C3w.\n` +
  `   Only propext, Classical.choice and Quot.sound are allowed.\n` +
  `6. Write lean/README.md:\n` +
  `   - what the snapshot is, and how to build it (one module at a time is safest; a cold parallel build can need about 12.5 GB);\n` +
  `   - a table of the modules grouped by topic (period 1; windows; black runs and strip certificates; Jen and masked Jen; diagonals; zero-boundary left half and period 2; ether and period 4; period 3; barriers), one line each, with headline theorem names;\n` +
  `   - which modules predate the 2026-10-15 attempt (check file birth times with \`stat -f %B\` and the docstrings).\n` +
  `   If the harness refuses to let you write README.md, return its full text in readme_text and set readme_written false; the coordinator will write it. Always fill readme_text either way.\n` +
  `7. Leave .lake/ in place; it is git-ignored. Do not touch the catalog or anything outside lean/ and ${TMP}/snapshot/. Wrap every command in \`timeout 60\`, and make sure no process you started is still running when you finish.`

const [audits, snap] = await parallel([
  () => parallel(GROUPS.map(g => () =>
    agent(auditPrompt(g), { label: `audit:${g.key}`, phase: 'Audit', schema: AUDIT_SCHEMA })
      .then(r => r && { group: g.key, ...r }))),
  () => agent(snapPrompt, { label: 'lean-snapshot', phase: 'Snapshot', schema: SNAP_SCHEMA }),
])

const auditList = (audits || []).filter(Boolean)
const allExclude = auditList.flatMap(a => a.exclude)
log(`audits returned ${auditList.length}/${GROUPS.length}; ${allExclude.length} exclusion entries`)

const [critic, snapV] = await parallel([
  () => agent(
    `You are a completeness critic for a git-commit exclusion list. Archive: ${ARCH}. It is about to be committed, with the exclusions below put in a .gitignore.\n\n` +
    `Audits (per directory: phase, purpose, exclusions):\n${JSON.stringify(auditList, null, 1)}\n\n` +
    `Check, read-only, and wrap every command in \`timeout 60\`:\n` +
    `1. Missed third-party content. Scan every .txt, .json, .tsv, .md and .out file under research/ NOT covered by an exclusion. Use heuristics: long prose, arXiv or journal headers, "Abstract", copyright lines, OCR artifacts, other authors' code or theorem lists. Open each suspect and judge it.\n` +
    `2. Wrongly excluded files: an excluded file that is our own work and small, or that a Lean file or verification needs.\n` +
    `3. Secrets: grep the whole archive (${ARCH}, including writeup/ and README.md) for credentials, tokens, private keys and email addresses, and judge each hit.\n` +
    `4. Phase assignments that look wrong given file times (\`stat -f %m\`) and contents. Round 1 ran roughly 04:40-07:10, round 2 06:30-09:40, the final batch from 09:46.\n` +
    `Give exact paths relative to ${ARCH}.`,
    { label: 'exclusion-critic', phase: 'Check', schema: CRITIC_SCHEMA }),
  () => snap && agent(
    `Adversarially verify a Lean snapshot at ${ARCH}/lean, which must hold byte-identical copies of the Rule 30 modules of the catalog at ${CAT}. When uncertain, count a claim as refuted.\n\n` +
    `Builder's report:\n${JSON.stringify(snap, null, 1)}\n\n` +
    `Check:\n` +
    `1. Every .lean file under lean/Ruliology is byte-identical to the catalog file at the same path; SHA256SUMS is correct and complete; no catalog module in the import closure of the snapshot root is missing.\n` +
    `2. The root lean/Ruliology.lean imports exactly the catalog root's Rule30* imports, in the same order. lakefile.toml and lean-toolchain are correct.\n` +
    `3. \`timeout 60 lake build --no-build\` in lean/ reports everything up to date. Recompile from source, one at a time with \`timeout 60 lake env lean <file>\` from lean/, the modules Rule30Prize, Rule30PeriodTwo, Rule30ZeroBoundaryWidth52, Rule30EtherTrapWidth20 and Rule30EtherThreeTrap.\n` +
    `4. #print axioms for the headline theorems (scratch file under ${TMP}/snapshot/verify/): only propext, Classical.choice and Quot.sound.\n` +
    `5. lean/README.md (or the readme_text above if the file is missing) is accurate: theorem names exist, topics and provenance are right, and nothing overclaims. Problem 1 is open and must be described as open.\n` +
    `Never run two Lean processes at once. Do not modify anything under ${ARCH} or ${CAT}. Wrap every command in \`timeout 60\`.`,
    { label: 'verify-snapshot', phase: 'Check', schema: SNAPV_SCHEMA }),
])

return { audits: auditList, snap, critic, snapV }
