export const meta = {
  name: 'r30-final-certify-p3',
  description: 'Rule 30: kernel-certify round-2 computational claims and build the least-period-3 ether framework, each adversarially verified',
  phases: [
    { title: 'Work', detail: 'kernel-certify-r2 and p3-ether workers' },
    { title: 'Verify', detail: 'adversarial recompile and statement audit per worker' },
  ],
}

const ROOT = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize'
const TASKS = [
  { key: 'certify', label: 'kernel-certify-r2', dir: `${ROOT}/kernel-certify-r2` },
  { key: 'p3', label: 'p3-ether', dir: `${ROOT}/p3-ether` },
]

const WORK_SCHEMA = {
  type: 'object',
  properties: {
    summary: { type: 'string' },
    lean_theorems: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          name: { type: 'string' },
          file: { type: 'string' },
          statement: { type: 'string' },
          meaning: { type: 'string' },
          compile_seconds: { type: 'number' },
          axioms: { type: 'string' },
        },
        required: ['name', 'file', 'statement', 'meaning', 'axioms'],
      },
    },
    computational_results: { type: 'array', items: { type: 'string' } },
    gaps: { type: 'array', items: { type: 'string' } },
    unconditional_progress_on_problem1: { type: 'string' },
    report_path: { type: 'string' },
  },
  required: ['summary', 'lean_theorems', 'computational_results', 'gaps', 'unconditional_progress_on_problem1', 'report_path'],
}

const VERIFY_SCHEMA = {
  type: 'object',
  properties: {
    checked: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          name: { type: 'string' },
          file: { type: 'string' },
          compiles: { type: 'boolean' },
          axioms_ok: { type: 'boolean' },
          no_sorry_or_tricks: { type: 'boolean' },
          statement_matches_claim: { type: 'boolean' },
          notes: { type: 'string' },
        },
        required: ['name', 'file', 'compiles', 'axioms_ok', 'no_sorry_or_tricks', 'statement_matches_claim', 'notes'],
      },
    },
    refuted_claims: { type: 'array', items: { type: 'string' } },
    overall: { type: 'string' },
  },
  required: ['checked', 'refuted_claims', 'overall'],
}

const results = await pipeline(
  TASKS,
  t => agent(
    `Your full task statement is in ${ROOT}/final_tasks/${t.key}.md. Read it first and follow it exactly, including every HARD constraint (each local command wrapped in \`timeout 60\`; scratch only under ${t.dir}/; never modify the Ruliology repo or ruliology-lean/Ruliology/; core Lean 4.30, no Mathlib, no native_decide; keep each Lean check under ~2 GB, and never run two Lean processes at once).\n\n` +
    `Before you return:\n` +
    `- write ${t.dir}/REPORT.md with every result: exact Lean statements, file paths, compile times, #print axioms output, and which parts remain computational or unproved;\n` +
    `- make sure no process you started is still running (check with \`pgrep -fl\` for your scratch path and kill leftovers);\n` +
    `- list in lean_theorems ONLY theorems whose files you compiled successfully yourself, with the axioms exactly as #print axioms printed them.\n` +
    `Honesty matters more than progress: if a target fails, say so plainly in gaps.`,
    { label: t.label, phase: 'Work', schema: WORK_SCHEMA },
  ),
  (w, t) => w && agent(
    `You are an adversarial verifier. Try to REFUTE the claims below; when uncertain, count the claim as refuted.\n\n` +
    `Task statement the worker received: ${ROOT}/final_tasks/${t.key}.md. Worker scratch dir: ${t.dir}/ (REPORT.md there).\n` +
    `Worker's structured result:\n${JSON.stringify(w, null, 2)}\n\n` +
    `For every theorem listed:\n` +
    `1. Recompile its file from /Users/swish/src/wolfram/vibe-proof/ruliology-lean with \`timeout 60 lake env lean <file>\`, one file at a time (the machine is memory-constrained; never run two Lean processes at once).\n` +
    `2. Get #print axioms for the theorem: copy the file into ${t.dir}/verify/ with \`#print axioms <name>\` appended and compile the copy. Only propext, Classical.choice and Quot.sound are allowed.\n` +
    `3. Grep the file and its non-catalog imports for sorry, admit, native_decide, axiom, implemented_by, extern, unsafe, opaque, debug.skipKernelTC and Lean.ofReduceBool.\n` +
    `4. Read the statement and its definitions. Does it say what the worker claims? Check that cell/rule definitions are rule 30 (new = left xor (center or right)), that hypotheses are satisfiable and not vacuous, that quantifiers are the right way round, and that "W", "phase" and similar parameters cover what the claim says.\n` +
    `Also spot-check the computational_results that matter most by rerunning or recomputing them independently where this fits in 60 s.\n` +
    `Write your notes to ${t.dir}/verify/VERDICT.md. Do not modify the worker's files. Never modify the Ruliology repo or ruliology-lean/Ruliology/. Wrap every command in \`timeout 60\`.`,
    { label: `verify:${t.label}`, phase: 'Verify', schema: VERIFY_SCHEMA },
  ).then(v => ({ task: t.label, work: w, verdict: v })),
)

return results.filter(Boolean)
