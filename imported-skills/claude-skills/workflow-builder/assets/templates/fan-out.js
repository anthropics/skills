export const meta = {
  name: 'fan-out-research',
  description: 'Fan out independent units, then synthesize',
  phases: [
    { title: 'Fan out' },
    { title: 'Synthesize' }
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


// Fan-out: independent units in parallel, then one synthesis.
const ITEMS = args?.items ?? ['item one', 'item two', 'item three']

phase('Fan out')
const results = await parallel(
  ITEMS.map((item, i) => () =>
    agent(`Do the unit of work for:\n${item}`,
          { label: `unit:${i + 1}`, model: 'haiku', schema: FINDINGS_SCHEMA }))
)

phase('Synthesize')
const clean = results.filter(Boolean)
const report = await agent(
  `Synthesize these results into one report:\n${JSON.stringify(clean)}`,
  { model: 'opus' }
)
log(`Done: synthesized ${clean.length} results.`)
return report

