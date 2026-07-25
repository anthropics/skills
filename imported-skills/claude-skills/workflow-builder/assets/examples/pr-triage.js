// Example workflow: triage open PRs for bugs before merge.
//
// Shape: fan-out (one reviewer per PR) -> skeptic-vote (verify each high-severity
// finding so a false positive doesn't waste review time) -> synthesize one report.
//
// Run: enable CLAUDE_CODE_WORKFLOWS=1, save under .claude/workflows/, launch via /workflows.
// Pass PR identifiers in via args, e.g. Workflow({ scriptPath, args: { prs: ['#12', '#15'] } }).

export const meta = {
  name: 'pr-triage',
  description: 'Triage open PRs for bugs before merge, with adversarial verification of high-severity findings',
  whenToUse: 'Run before a merge window to surface and confirm likely bugs across open PRs',
  phases: [
    { title: 'Review', detail: 'One reviewer agent per PR', model: 'haiku' },
    { title: 'Verify', detail: 'Skeptic vote on high-severity findings', model: 'sonnet' },
    { title: 'Report', detail: 'Synthesize a single triage report', model: 'opus' }
  ]
}

const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    pr: { type: 'string' },
    findings: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          title: { type: 'string' },
          severity: { type: 'string', enum: ['low', 'medium', 'high'] },
          file: { type: 'string' }
        },
        required: ['title', 'severity']
      }
    }
  },
  required: ['pr', 'findings']
}

const VERDICT_SCHEMA = {
  type: 'object',
  properties: { refuted: { type: 'boolean' }, reason: { type: 'string' } },
  required: ['refuted']
}

// args.prs is the list of PR identifiers to triage; gathering their diffs happens
// inside each reviewer agent (the orchestrator has no filesystem/network access).
const PRS = args?.prs ?? ['#101', '#102', '#103']

// Phase 1 — fan out one reviewer per PR. Cheap model, structured output.
phase('Review')
const reviews = await parallel(
  PRS.map((pr, i) => () =>
    agent(
      `Review PR ${pr} for likely bugs. Inspect the diff and report concrete findings.`,
      { label: `review:${pr}`, phase: 'Review', model: 'haiku', schema: FINDINGS_SCHEMA }
    )
  )
)

// Collect every high-severity finding across all PRs.
const highSeverity = reviews
  .filter(Boolean)
  .flatMap(r => (r.findings ?? []).map(f => ({ ...f, pr: r.pr })))
  .filter(f => f.severity === 'high')

log(`Reviewed ${reviews.filter(Boolean).length} PRs; ${highSeverity.length} high-severity findings to verify.`)

// Phase 2 — skeptic vote: three independent agents try to refute each high finding.
// A finding survives only if it is NOT refuted by a majority.
phase('Verify')
const confirmed = []
for (let i = 0; i < highSeverity.length; i++) {
  const f = highSeverity[i]
  const votes = await parallel(
    Array.from({ length: 3 }, (_, k) => () =>
      agent(
        `Try hard to REFUTE this bug claim about PR ${f.pr}: "${f.title}" in ${f.file ?? 'unknown file'}. ` +
        `Return { refuted: boolean, reason }.`,
        { label: `skeptic:${i + 1}.${k + 1}`, phase: 'Verify', model: 'sonnet', schema: VERDICT_SCHEMA }
      )
    )
  )
  const survives = votes.filter(v => v && !v.refuted).length >= 2
  if (survives) confirmed.push(f)
}

log(`Verified findings: ${confirmed.length} of ${highSeverity.length} survived the skeptic vote.`)

// Phase 3 — synthesize one report from the confirmed findings.
phase('Report')
const report = await agent(
  `Write a concise PR-triage report. Group by PR. Only include these confirmed high-severity findings:\n` +
  JSON.stringify(confirmed, null, 2),
  { model: 'opus' }
)

return { report, confirmed, reviewed: reviews.filter(Boolean).length }
