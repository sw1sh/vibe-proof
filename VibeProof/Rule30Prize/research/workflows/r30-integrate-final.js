export const meta = {
  name: 'r30-integrate-final',
  description: 'Integrate the verified final-batch Rule 30 Lean results into the ruliology-lean catalog, verify the integration, and update the write-up',
  phases: [
    { title: 'Integrate', detail: 'rename and add new modules to the catalog, one build at a time' },
    { title: 'Check', detail: 'adversarial integration check and write-up update' },
  ],
}

const R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize'
const CAT = '/Users/swish/src/wolfram/vibe-proof/ruliology-lean'
const ARCH = '/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize'

const INTEG_SCHEMA = {
  type: 'object',
  properties: {
    summary: { type: 'string' },
    new_files: { type: 'array', items: { type: 'object', properties: {
      path: { type: 'string' }, module: { type: 'string' }, sha256: { type: 'string' },
      compile_seconds: { type: 'number' }, peak_gb: { type: 'number' } },
      required: ['path', 'module', 'sha256'] } },
    name_map: { type: 'array', items: { type: 'object', properties: {
      scratch: { type: 'string' }, catalog: { type: 'string' } }, required: ['scratch', 'catalog'] } },
    main_theorems: { type: 'array', items: { type: 'object', properties: {
      name: { type: 'string' }, statement: { type: 'string' }, axioms: { type: 'string' } },
      required: ['name', 'statement', 'axioms'] } },
    root_import_count: { type: 'number' },
    not_integrated: { type: 'array', items: { type: 'string' } },
    problems: { type: 'array', items: { type: 'string' } },
  },
  required: ['summary', 'new_files', 'name_map', 'main_theorems', 'root_import_count', 'not_integrated', 'problems'],
}

const VERIFY_SCHEMA = {
  type: 'object',
  properties: {
    existing_files_unchanged: { type: 'boolean' },
    changed_existing: { type: 'array', items: { type: 'string' } },
    modules: { type: 'array', items: { type: 'object', properties: {
      module: { type: 'string' }, compiles: { type: 'boolean' }, seconds: { type: 'number' },
      axioms_ok: { type: 'boolean' }, no_tricks: { type: 'boolean' },
      statements_match_scratch: { type: 'boolean' }, notes: { type: 'string' } },
      required: ['module', 'compiles', 'axioms_ok', 'no_tricks', 'statements_match_scratch', 'notes'] } },
    full_build_ok: { type: 'boolean' },
    refuted: { type: 'array', items: { type: 'string' } },
    overall: { type: 'string' },
  },
  required: ['existing_files_unchanged', 'changed_existing', 'modules', 'full_build_ok', 'refuted', 'overall'],
}

const WRITEUP_SCHEMA = {
  type: 'object',
  properties: {
    path: { type: 'string' },
    sections_changed: { type: 'array', items: { type: 'string' } },
    stale_claims_fixed: { type: 'array', items: { type: 'string' } },
    size_kb: { type: 'number' },
    notes: { type: 'string' },
  },
  required: ['path', 'sections_changed', 'stale_claims_fixed', 'size_kb', 'notes'],
}

phase('Integrate')
const integ = await agent(
  `Integrate verified Rule 30 results into the Lean catalog at ${CAT} (lake project \`ruliology\`, core Lean 4.30, no Mathlib).\n\n` +
  `Read first: ${R}/kernel-certify-r2/REPORT.md and ${R}/p3-ether/REPORT.md. Both results were adversarially verified; the verdicts are at the end of each report.\n\n` +
  `Sources (all already compile against the current catalog):\n` +
  `- ${R}/kernel-certify-r2/t1/src/KC: Q01Lanes.lean (soundness of the bit-sliced checker); Q01W52.lean + Q01W52/C*.lean (256 chunk theorems \`check 52 K 18 c = true\` in 16 files); Q01W56 (do NOT integrate W56: 1024 chunks, 345 s of kernel time, too heavy for the catalog).\n` +
  `- ${R}/kernel-certify-r2/t2/src/KC: StripeFront, StripeCycles0/1/2, StripeFamily.\n` +
  `- ${R}/kernel-certify-r2/t3/src/KC: EtherTrap and its certificate files.\n` +
  `- ${R}/kernel-certify-r2/t4/src/KC: PeriodTwoLang, PeriodTwoW5, PeriodTwoW6.\n` +
  `- ${R}/p3-ether/lean: P3Ether, P3NoWall, P3Trap001, P3Reach, P3Left, P3Skel (namespace Ruliology.CellularAutomata.Rule30EtherThree).\n` +
  `Each tN directory has a build.sh showing how its modules were compiled.\n\n` +
  `Do:\n` +
  `1. Study the catalog's conventions: the root Ruliology.lean, Ruliology/CellularAutomata/Rule30*.lean (module docstrings, namespaces such as Ruliology.CellularAutomata.Rule30ZeroBoundary), and the Rule104Complexity/ subdirectory used for multi-file data.\n` +
  `2. Create new catalog modules with Rule30-prefixed names, for example Rule30ZeroBoundaryLanes, Rule30ZeroBoundaryWidth52, Rule30ZeroBoundaryStripeFront, Rule30EtherTrap, Rule30PeriodTwoLanguage, and Rule30EtherThree, Rule30EtherThreeNoWall, Rule30EtherThreeTrap, Rule30EtherThreeReach, Rule30EtherThreeLeft, Rule30EtherThreeSkeleton. Put heavy data (W52 chunks, stripe cycles, trap certificates) in a subdirectory Ruliology/CellularAutomata/Rule30Certificates/. Regroup the 256 W52 chunk theorems into 4 data modules of 64 each; if one such module takes more than about 40 s, use 8 modules of 32. Rename namespaces to the catalog's style and fix all imports.\n` +
  `3. Change only names. Keep every theorem statement and proof equivalent. No sorry, no native_decide, no new axioms; decide +kernel only. Give each module a docstring that says what it proves and where it came from (final batch, 2026-10-15). The Width52 docstring must say that W ≤ 56 was also kernel-checked and lives, with its build script, in ${ARCH}/research/kernel-certify-r2/t1. It is not in the catalog because of build cost.\n` +
  `4. Do not modify any existing file under Ruliology/. The only existing file you may change is the root Ruliology.lean, to add imports. Put any helper lemma you need in your new module.\n` +
  `5. Build each new module ONE AT A TIME: \`timeout 60 /usr/bin/time -l lake build Ruliology.CellularAutomata.<Module>\` from ${CAT}. Never run two Lean or lake processes at once; the machine is short on memory. Then add the imports to Ruliology.lean and run \`timeout 60 lake build\`; everything should already be built.\n` +
  `6. For the main theorems, compile a scratch file under ${R}/integrate-final/ that imports the new modules and runs #print axioms. Only propext, Classical.choice and Quot.sound are allowed.\n` +
  `7. Return every new file with its SHA-256 (\`shasum -a 256\`), compile time and peak memory; the scratch-to-catalog name map; the main theorems with their full statements and axioms; and anything you did not integrate, with the reason.\n` +
  `Never touch /Users/swish/src/wolfram/Ruliology; another session owns it. Wrap every command in \`timeout 60\`. Make sure no process you started is still running when you finish.`,
  { label: 'integrate-final', phase: 'Integrate', schema: INTEG_SCHEMA },
)

if (!integ) return { error: 'integrator returned nothing' }

phase('Check')
const [verdict, writeup] = await parallel([
  () => agent(
    `Adversarially verify the integration of new Rule 30 modules into the Lean catalog at ${CAT}. When uncertain, count a claim as refuted.\n\n` +
    `Integrator's report:\n${JSON.stringify(integ, null, 2)}\n\n` +
    `Checks:\n` +
    `1. Existing files: recompute \`shasum -a 256\` for every file listed in ${R}/integrate-final/catalog_before.sha256 (paths relative to ${CAT}). Only Ruliology.lean may differ.\n` +
    `2. Recompile each new module one at a time with \`timeout 60 lake env lean <file>\` from ${CAT}, and record the time. Never run two Lean processes at once.\n` +
    `3. Run #print axioms for the main theorems from a scratch file under ${R}/integrate-final/verify/ that imports the modules; compile it with \`timeout 60 lake env lean\`. Only propext, Classical.choice and Quot.sound are allowed.\n` +
    `4. Grep the new files for sorry, admit, native_decide, axiom, implemented_by, extern, unsafe, opaque, skipKernelTC, ofReduceBool and set_option.\n` +
    `5. Compare each main theorem's statement with the verified scratch version (${R}/kernel-certify-r2/t1..t4/src/KC and ${R}/p3-ether/lean). The integration may only rename; flag any weakened or changed statement. Check that the regrouped W52 chunk theorems cover every chunk index exactly once, with the same parameters as the scratch Q01W52 files, and that the main W52 theorem consumes all of them.\n` +
    `6. Confirm \`timeout 60 lake build\` succeeds with the root importing the new modules.\n` +
    `Write only under ${R}/integrate-final/verify/. Do not modify the catalog. Wrap every command in \`timeout 60\`.`,
    { label: 'verify-integration', phase: 'Check', schema: VERIFY_SCHEMA },
  ),
  () => agent(
    `Update the Rule 30 write-up at ${ARCH}/writeup/rule30-state.html with the final batch. It is a self-contained HTML page written in round 2, about 276 KB.\n\n` +
    `Sources: ${R}/kernel-certify-r2/REPORT.md, ${R}/p3-ether/REPORT.md, and this integration report, which gives the catalog names:\n${JSON.stringify(integ, null, 2)}\n\n` +
    `Do:\n` +
    `- Add a section on the final batch:\n` +
    `  - Q01 is kernel-checked for widths ≤ 52 in the catalog and ≤ 56 in the archive;\n` +
    `  - the stripe-prefix family;\n` +
    `  - the pure ether lies in no trap of width ≤ 20;\n` +
    `  - the period-2 free-bit constraints at widths 5 and 6;\n` +
    `  - period 3: the 12×3 ether and its complete alignments; no wall of width ≤ 12 (Lean) or ≤ 28 (search); the 47-cell, period-21 trap t001 for 001, which every one of 18,258 runs entered (max delay about 2·10^5), while 011 never became periodic; the left-side reductions Q001, C3s001 and C3w011 with death-time searches; the skeletons.\n` +
    `- Add the new theorems to the theorem table under their catalog names.\n` +
    `- Fix statements elsewhere on the page that the new results supersede, for example "Q01 is checked only to width 16" or "period 3 has not been attacked".\n` +
    `- Keep the framing honest. Problem 1 is open, and nothing here excludes any period unconditionally. Include the verifiers' corrections: no wall is known only up to width 28; minimality of t001 is open; AbsorptionT t001, Q001, C3s001 and C3w011 are open.\n` +
    `- Keep the page self-contained, valid and in its existing style. Add no external resources. If ${R}/writeup-r2/checkhtml.py fits, use it to check the page.\n` +
    `- Change nothing except that HTML file.`,
    { label: 'writeup-final', phase: 'Check', schema: WRITEUP_SCHEMA },
  ),
])

return { integ, verdict, writeup }
