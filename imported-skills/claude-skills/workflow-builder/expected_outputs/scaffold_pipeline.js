export const meta = {
  name: 'pr-triage',
  description: 'Triage open PRs for bugs',
  phases: [
    { title: 'Triage' },
    { title: 'Verify' }
  ]
}


const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    findings: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          title: { type: 'string' },
          severity: { type: 'string', enum: ['low', 'medium', 'high'] }
        },
        required: ['title']
      }
    }
  },
  required: ['findings']
}


// Pipeline: each item flows through stages independently (no barrier).
const ITEMS = args?.items ?? ['item one', 'item two', 'item three']

const results = await pipeline(
  ITEMS,
  // Stage 1 — triage / extract (cheap, high volume).
  (item, _orig, i) =>
    agent(`Triage:\n${item}`, { label: `triage:${i + 1}`, phase: 'Triage', model: 'haiku', schema: FINDINGS_SCHEMA }),
  // Stage 2 — verify / refine each finding (fewer items, more judgement).
  (prev) =>
    parallel((prev?.findings ?? []).map(f => () =>
      agent(`Verify and refine: ${f.title}`, { phase: 'Verify', model: 'sonnet' })))
)

log(`Done: processed ${results.filter(Boolean).length} items through the pipeline.`)
return results.filter(Boolean)

