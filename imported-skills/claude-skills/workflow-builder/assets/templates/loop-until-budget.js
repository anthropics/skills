export const meta = {
  name: 'loop-until-budget',
  description: 'Discover items under a budget guard',
  phases: [
    { title: 'Discover' }
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


// Loop: discover an unknown number of items. GUARDED against the agent cap.
const found = []
const seen = new Set()
let dryRounds = 0
const HARD_CAP = 100

phase('Discover')
while (
  dryRounds < 2 &&
  found.length < HARD_CAP &&
  (!budget.total || budget.remaining() > 50_000)
) {
  const r = await agent(
    `Find items NOT already found:\n${JSON.stringify([...seen])}`,
    { model: 'sonnet', schema: FINDINGS_SCHEMA }
  )
  const fresh = (r?.findings ?? []).filter(f => !seen.has(f.title))
  fresh.forEach(f => seen.add(f.title))
  found.push(...fresh)
  dryRounds = fresh.length === 0 ? dryRounds + 1 : 0
  log(`Round complete: ${fresh.length} new, ${found.length} total.`)
}
return found

