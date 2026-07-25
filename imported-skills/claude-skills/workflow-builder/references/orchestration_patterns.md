# Orchestration Patterns

Copy-paste shapes for the common multi-agent topologies. Pick by answering the topology questions in [decision_and_intake_guide.md](decision_and_intake_guide.md), then adapt one of these.

## 1. Fan-out then synthesize

**When:** a known list of independent items, one pass each, and you need one combined answer at the end.

```js
const findings = await parallel(
  questions.map((q, i) => () =>
    agent(`Research and report verified facts:\n\n${q}`,
          { label: `q${i + 1}`, schema: RESEARCH_SCHEMA }))
)
const report = await agent(
  `Synthesize these findings into one report:\n${JSON.stringify(findings.filter(Boolean))}`,
  { model: 'opus' }
)
```

## 2. Pipeline: stage then stage (no barrier)

**When:** items progress through ordered stages and each item should advance the instant it's ready, not wait for siblings.

```js
const results = await pipeline(
  DIMENSIONS,
  d => agent(d.prompt, { label: `review:${d.key}`, phase: 'Review', schema: FINDINGS_SCHEMA }),
  review => parallel((review?.findings ?? []).map(f => () =>
    agent(`Adversarially verify: ${f.title}`, { schema: VERDICT_SCHEMA })))
)
```

## 3. Barrier when you must dedup / merge first

**When:** the next stage needs the *entire* previous result set in hand — to dedup, merge, or early-exit on a count.

```js
const all = await parallel(DIMENSIONS.map(d => () => agent(d.prompt, { schema: FINDINGS_SCHEMA })))
const deduped = dedupeByFileAndLine(all.filter(Boolean).flatMap(r => r.findings))
const summary = await agent(`Summarize ${deduped.length} unique findings:\n${JSON.stringify(deduped)}`)
```

## 4. Loop until target count

**When:** discovery with a fixed goal ("find 10 bugs"). Always bound it.

```js
const bugs = []
while (bugs.length < 10 && bugs.length < 100 /* hard cap guard */) {
  const r = await agent(
    `Find bugs NOT already listed:\n${JSON.stringify(bugs)}`,
    { schema: BUGS_SCHEMA }
  )
  if (!r?.bugs?.length) break
  bugs.push(...r.bugs)
}
```

## 5. Loop until budget runs low

**When:** depth should scale to the user's token target. The `budget` guard is essential.

```js
const issues = []
while (budget.total && budget.remaining() > 50_000) {
  const r = await agent('Find one more issue not yet reported...', { schema: ISSUE_SCHEMA })
  if (!r?.issues?.length) break
  issues.push(...r.issues)
}
```

## 6. Adversarial verification (skeptic vote)

**When:** a finding will be acted on and a plausible-but-wrong one is costly. Findings survive on majority vote.

```js
const votes = await parallel(Array.from({ length: 3 }, (_, i) => () =>
  agent(`Try hard to REFUTE this claim, return { refuted: boolean }:\n${claim}`,
        { label: `skeptic:${i + 1}`, schema: VERDICT_SCHEMA })))
const survives = votes.filter(v => v && !v.refuted).length >= 2
```

## 7. Judge panel

**When:** a wide solution space benefits from several independent attempts, scored and synthesized.

```js
const drafts = await parallel(ANGLES.map(a => () =>
  agent(`Produce a plan. Take a strictly ${a} approach.`)))
const scored = await parallel(drafts.map((d, i) => () =>
  agent(`Score this plan 1-10 with reasons:\n${d}`, { label: `judge:${i + 1}`, schema: SCORE_SCHEMA })))
const winner = drafts[scored.indexOf(scored.reduce((a, b) => (a?.score ?? 0) >= (b?.score ?? 0) ? a : b))]
const final = await agent(`Refine the winning plan:\n${winner}`, { model: 'opus' })
```

## 8. Loop until dry

**When:** unknown-size discovery that stops after K consecutive rounds with no new findings.

```js
const found = []
const seen = new Set()
let dryRounds = 0
while (dryRounds < 2 && found.length < 100) {
  const r = await agent(`Find items not in:\n${JSON.stringify([...seen])}`, { schema: ITEMS_SCHEMA })
  const fresh = (r?.items ?? []).filter(x => !seen.has(x.id))
  fresh.forEach(x => seen.add(x.id))
  found.push(...fresh)
  dryRounds = fresh.length === 0 ? dryRounds + 1 : 0
}
```

## 9. Nested workflow

**When:** a self-contained sub-job lives inside a larger one (one level deep maximum).

```js
const research = await workflow('research-fanout', ['question one', 'question two'])
```

## Schema declarations

Schemas are plain JSON Schema objects defined as top-level `const`s and passed via `{ schema }`:

```js
const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
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
  required: ['findings']
}
```

Between stages, stringify structured data into the next prompt (`JSON.stringify(...)`); the schema only shapes what comes *back* from a single `agent()` call.

---

## Sources

1. Ray Amjad — `claude-code-workflow-creator`, `references/patterns.md` (fan-out, pipeline, judge-panel, loop shapes).
2. Anthropic — Claude Code Workflow tool documentation (`pipeline`/`parallel` semantics).
3. Anthropic — sub-agent orchestration patterns (Agent tool, fresh-context isolation).
4. Karpathy — LLM agent loop / file-optimization patterns (loop-until-dry analogue).
5. Google SRE Workbook — error budgets (loop-until-budget guard).
6. "LLM-as-a-judge" evaluation literature (judge-panel + scored synthesis).
7. Ensemble / majority-vote methods in ML (skeptic-vote verification).
8. JSON Schema specification — structured-output contract for the `schema` option.
