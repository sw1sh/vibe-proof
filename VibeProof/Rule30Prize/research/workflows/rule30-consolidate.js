export const meta = {
  name: 'rule30-consolidate',
  description: 'Consolidate the Rule 30 Problem 1 attempt: stage round-2 Lean modules (deduplicated) and write the state-of-the-attack document',
  phases: [
    { title: 'Consolidate', detail: 'integrate-r2 (Lean staging) and writeup-r2 (document) in parallel' },
  ],
}
const ARGS = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/consolidate_args.json'
const lead = key => `Your complete task specification is stored as the JSON string under key "${key}" in the file ${ARGS}. First print it with \`python3 -I -c "import json; print(json.load(open('${ARGS}'))['${key}'])"\` and then carry out that specification exactly, including all of its HARD constraints (every local command under 60 s via \`timeout 60\`; never modify ruliology-lean/Ruliology/ or the Ruliology repo; scratch only in the directories it names). Return the structured result.`
const CURATE_SCHEMA = { type: 'object', properties: {
  staging_dir: { type: 'string' },
  modules: { type: 'array', items: { type: 'object', properties: {
    file: { type: 'string' }, namespace: { type: 'string' }, main_theorems: { type: 'string' },
    axioms: { type: 'string' }, build_seconds: { type: 'number' }, imports: { type: 'string' } },
    required: ['file', 'main_theorems', 'axioms'] } },
  removed_duplicates: { type: 'string' }, import_lines: { type: 'string' },
  summary: { type: 'string' } }, required: ['staging_dir', 'modules', 'summary'] }
const WRITE_SCHEMA = { type: 'object', properties: {
  file: { type: 'string' }, sections: { type: 'array', items: { type: 'string' } },
  theorem_count: { type: 'number' }, summary: { type: 'string' } }, required: ['file', 'summary'] }
phase('Consolidate')
const [integ, write] = await parallel([
  () => agent(lead('integrate'), { label: 'integrate-r2', phase: 'Consolidate', schema: CURATE_SCHEMA }),
  () => agent(lead('writeup'), { label: 'writeup-r2', phase: 'Consolidate', schema: WRITE_SCHEMA }),
])
return { integ, write }
